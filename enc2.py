

def gamma_encode(choices, nr_candidates=None, max_choices=None):
    nr_choices = len(choices)
    nr_candidates, max_choices = \
        get_choice_params(nr_choices, nr_candidates, max_choices)
    if not nr_choices:
        return 0

    offsets = get_offsets(nr_candidates)
    sumus = offsets[nr_choices - 1]

    b = nr_candidates - nr_choices
    i = 1
    while 1:
        sumus += choices[-i] * get_factor(b, i)
        if i >= nr_choices:
            break
        i += 1

    return sumus

#returns the encoded selection of the users vote called in mk_random_vote
def encode_selection(selection, nr_candidates=None):
    if nr_candidates is None:
        nr_candidates = len(selection)
    return gamma_encode(selection, nr_candidates, nr_candidates)


#encryption that returns a,b,r called in vote_for_encoded
def encrypt(message, modulus, generator, order, public, randomness=None):
    if randomness is None:
        randomness = get_random_int(1, order)
    message = message + 1
    if message >= order:
        m = "message is too large"
        raise ValueError(m)

    legendre = pow(message, order, modulus)
    if legendre != 1:
        message = -message % modulus
    alpha = pow(generator, randomness, modulus)
    beta = (message * pow(public, randomness, modulus)) % modulus
    return [alpha, beta, randomness]

#does the encryption,proof ,encrypted ballot and returns the vote with voter name and eb called in mk_random_vote
def vote_from_encoded(modulus, generator, order, public,
                      voter, encoded, nr_candidates,
                      audit_code=None, publish=None):

    alpha, beta, rnd = encrypt(encoded, modulus, generator, order, public)
    proof = prove_encryption(modulus, generator, order, alpha, beta, rnd)
    commitment, challenge, response = proof
    eb = {'modulus': modulus,
          'generator': generator,
          'order': order,
          'public': public,
          'alpha': alpha,
          'beta': beta,
          'commitment': commitment,
          'challenge': challenge,
          'response': response}

    fingerprint = numbers_hash((modulus, generator, alpha, beta,
                                commitment, challenge, response))
    vote = {'voter': voter,
            'fingerprint': fingerprint,
            'encrypted_ballot': eb}

    if audit_code:
        vote['audit_code'] = audit_code

    if publish:
        vote['voter_secret'] = rnd

    return vote


class ZeusCoreElection(object):

    def add_voters(self, *voters):
        name_set = set(v[0] for v in self.do_get_voters().itervalues())
        intersection = name_set.intersection(v[0] for v in voters)
        if intersection:
            m = "Voter '%s' already exists!" % (intersection.pop(),)
            raise ZeusError(m)

        new_voters = {}
        voter_audit_codes = {}
        for name, weight in voters:
            voter_key = "%x" % get_random_int(2, VOTER_KEY_CEIL)
            new_voters[voter_key] = (name, weight)
            audit_codes = list(get_random_int(2, VOTER_SLOT_CEIL)
                               for _ in xrange(3))
            voter_audit_codes[voter_key] = audit_codes
        self.do_store_voters(new_voters)
        self.do_store_voter_audit_codes(voter_audit_codes)

    def set_voting(self):
        stage = self.do_get_stage()
        if stage == 'VOTING':
            m = "Already in stage 'VOTING'"
            raise ZeusError(m)
        if stage != 'CREATING':
            m = "Cannot transition from stage '%s' to 'VOTING'" % (stage,)
            raise ZeusError(m)

        if not self.get_option('no_verify'):
            self.validate_creating()
        self.do_set_stage('VOTING')

    ### CLIENT REFERENCE ###

    def mk_random_vote(self, selection=None, voter=None,
                             audit_code=None, publish=None):
    	#???
        modulus, generator, order = self.do_get_cryptosystem()
        #need public key
        public = self.do_get_election_public()
        candidates = self.do_get_candidates()
        nr_candidates = len(candidates)
        #change to every choice
        if selection is None:
            r = get_random_int(0, 4)
            if r & 1:
                selection = get_random_selection(nr_candidates, full=0)
            else:
                selection = get_random_party_selection(nr_candidates, 2)

        voters = None
        if voter is None:
            voters = self.do_get_voters()
            voter = rand_choice(voters.keys())
        encoded = encode_selection(selection, nr_candidates)
        valid = True
        if audit_code:
            if voters is None:
                voters = self.do_get_voters()
            voter_audit_codes = self.do_get_voter_audit_codes(voter)
            if audit_code < 0:
                if voter not in voters:
                    m = ("Valid audit_code requested but voter not found!")
                    raise ValueError(m)
                audit_code = voter_audit_codes[0]
            elif voter not in voters:
                valid = False
            elif audit_code not in voter_audit_codes:
                valid = False
        vote = vote_from_encoded(modulus, generator, order, public,
                                 voter, encoded, nr_candidates,
                                 audit_code=audit_code, publish=1)
        rnd = vote['voter_secret']
        if not publish:
            del vote['voter_secret']

        return vote, selection, encoded if valid else None, rnd

     def mk_stage_creating(self, teller=_teller):
        nr_candidates = self._nr_candidates
        candidates = []
        append = candidates.append
        mid = nr_candidates // 2
        first = 1
        for i in xrange(0, mid):
            if first:
                append("Party-A" + PARTY_SEPARATOR + "0-2, 0")
                first = 0
            append("Party-A" + PARTY_SEPARATOR + "Candidate-%04d" % i)

        first = 1
        for i in xrange(mid, nr_candidates):
            if first:
                append("Party-B" + PARTY_SEPARATOR + "0-2, 1")
                first = 0
            append("Party-B" + PARTY_SEPARATOR + "Candidate-%04d" % i)

        voter_range = xrange(self._nr_voters)
        voters = [(("Voter-%08d" % x), 1) for x in voter_range]

        self.create_zeus_key()
        self.add_candidates(*candidates)
        self.add_voters(*voters)

    def mk_stage_voting(self, teller=_teller):
        selections = []
        plaintexts = {}
        votes = []
        voters = list(self.do_get_voters())
        for i, voter in zip(xrange(self._nr_votes), cycle(voters)):
            kw = {'audit_code': -1} if (i & 1) else {}
            kw['voter'] = voter
            vote, selection, encoded, rnd = self.mk_random_vote(**kw)
            if vote['voter'] != voter:
                m = "Vote has wrong voter!"
                raise AssertionError(m)


    @classmethod
    def mk_random(cls, nr_candidates   =   3,
                       nr_voters       =   10,
                       nr_votes        =   10,
                       nr_rounds       =   8,
                       stage           =   'FINISHED',
                       teller=_teller, **kw):

        self = cls(teller=teller, **kw)
        self._nr_candidates = nr_candidates
        self._nr_voters = nr_voters
        self._nr_votes = nr_votes
        self._nr_rounds = nr_rounds
        stage = stage.upper()

        with teller.task("Creating election"):
            self.mk_stage_creating(teller=teller)
        if stage == 'CREATING':
            return self

        self.set_voting()
        with teller.task("Voting", total=nr_votes):
            self.mk_stage_voting(teller=teller)
        if stage == 'VOTING':
            return self

def main():
	import argparse
	description='Zeus Election Reference Implementation and Verifier.'
	epilog="Try 'zeus --generate'"
	parser = argparse.ArgumentParser(description=description, epilog=epilog)

	parser.add_argument('--generate', nargs='*', metavar='outfile',
        help="Generate a random election and write it out in JSON")

	parser.add_argument('--candidates', type=int, default=3,
                        dest='nr_candidates',
                        help="Generate: Number of candidates")

	parser.add_argument('--voters', type=int, default=10,
                        dest='nr_voters',
                        help="Generate: Number of voters")

	args = parser.parse_args()

	def main_generate(args, teller=_teller, nr_parallel=0):
        filename = args.generate
        filename = filename[0] if filename else None
        no_verify = args.no_verify

        election = ZeusCoreElection.mk_random(
                            nr_candidates   =   args.nr_candidates,
                            nr_trustees     =   args.nr_trustees,
                            nr_voters       =   args.nr_voters,
                            nr_votes        =   args.nr_votes,
                            nr_rounds       =   args.nr_rounds,
                            stage           =   args.stage,
                            teller=teller, nr_parallel=nr_parallel,
                            no_verify=no_verify)
        exported, stage = election.export()

    teller_stream = TellerStream(outstream=outstream,
                                 output_interval_ms=args.oms,
                                 buffering=not args.no_buffer,
                                 buffer_feeds=args.buffer_feeds)
    teller = Teller(outstream=teller_stream)
    if args.no_buffer:
        Teller.eol = '\n'
        Teller.feed = '\n'

    if args.generate is not None:
        return main_generate(args, teller=teller, nr_parallel=nr_parallel)

    teller_stream.flush()
    