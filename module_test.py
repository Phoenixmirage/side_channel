#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys
PYTHON_MAJOR = sys.version_info[0]
from timeit import default_timer as timer
from datetime import datetime
from random import randint, choice as rand_choice
from collections import deque
from hashlib import sha256, sha1
from itertools import izip, izip_longest, cycle, chain, repeat
from math import log
import Crypto.Util.number as number
from Crypto import Random

from time import time, sleep

_random_generator_file = Random.new()

bit_length = lambda num: num.bit_length()
if sys.version_info < (2, 7):
    def bit_length(num):
        s = bin(num)
        s = s.lstrip('-0b')
        return len(s)

def c2048():
    p = 19936216778566278769000253703181821530777724513886984297472278095277636456087690955868900309738872419217596317525891498128424073395840060513894962337598264322558055230566786268714502738012916669517912719860309819086261817093999047426105645828097562635912023767088410684153615689914052935698627462693772783508681806906452733153116119222181911280990397752728529137894709311659730447623090500459340155653968608895572426146788021409657502780399150625362771073012861137005134355305397837208305921803153308069591184864176876279550962831273252563865904505239163777934648725590326075580394712644972925907314817076990800469107L
    q = (p - 1) / 2
    g0 = 9413060360466448686039353223715000895476653994878292629580005715413149309413036670654764332965742884842644976907757623558004566639402772235441684360505344528020498265000752015019397070007216279360736764344882321624397028370364113905272387950790871846302871493514381824738727519597460997038917208851728646071589006043553117796202327835258471557309074326286364547643265711871602511049432774864712871101230345650552324151494772279651818096255453921354231946373043379760842748887723994561573824188324702878924365252191380946510359485948529040410642676919518011031107993744638249385966735471272747905107277767654692463409L
    g = pow(g0, 2, p)
    x = 1469094658184849175779600697490107440856998313689389490776822841770551060089241836869172678278809937016665355003873748036083276189561224629758766413235740137792419398556764972234641620802215276336480535455350626659186073159498839187349683464453803368381196713476682865017622180273953889824537824501190403304240471132731832092945870620932265054884989114885295452717633367777747206369772317509159592997530169042333075097870804756411795033721522447406584029422454978336174636570508703615698164528722276189939139007204305798392366034278815933412668128491320768153146364358419045059174243838675639479996053159200364750820L
    y = pow(g, x, p)
    return p, q, g, x, y

#p, q, g, x, y = c2048()

# -------------------------FUNCTIONS--------------------------------------------------------
_terms = {}

def get_term(n, k):
    if k >= n:
        return 1

    if n in _terms:
        t = _terms[n]
        if k in t:
            return t[k]
    else:
        t = {n: 1}
        _terms[n] = t

    m = k
    while 1:
        m += 1
        if m in t:
            break

    term = t[m]
    while 1:
        term *= m
        m -= 1
        t[m] = term
        if m <= k:
            break

    return term

def strbin_to_int_mul(string):
    # lsb
    s = 0
    base = 1
    for c in string:
        s += ord(c) * base
        base *= 256

    return s

def strbin_to_int_native(string):
    return int.from_bytes(string)

if PYTHON_MAJOR == 3:
    strbin_to_int = strbin_to_int_native
else:
    strbin_to_int = strbin_to_int_mul

_offsets = {}

def get_offsets(n):
    if n in _offsets:
        return _offsets[n]

    offsets = []
    append = offsets.append
    sumus = 0
    i = 0
    while 1:
        sumus += get_term(n, n-i)
        append(sumus)
        if i == n:
            break
        i += 1

    _offsets[n] = offsets
    return offsets

_factors = {}

def get_factor(b, n):
    if n <= 1:
        return 1

    if b in _factors:
        t = _factors[b]
        if n in t:
            return t[n]
    else:
        t = {1: 1}
        _factors[b] = t

    i = n
    while 1:
        i -= 1
        if i in t:
            break

    f = t[i]
    while 1:
        f *= b + i
        i += 1
        t[i] = f
        if i >= n:
            break
    return f

def get_random_int(minimum, ceiling):
    top = ceiling - minimum
    nr_bits = bit_length(top)
    nr_bytes = (nr_bits - 1) / 8 + 1
    strbin = _random_generator_file.read(nr_bytes)
    num = strbin_to_int(strbin)
    shift = bit_length(num) - nr_bits
    if shift > 0:
        num >>= shift
    if num >= top:
        num -= top
    return num + minimum


def get_choice_params(nr_choices, nr_candidates=None, max_choices=None):
    if nr_candidates is None:
        nr_candidates = nr_choices
    if max_choices is None:
        max_choices = nr_candidates

    if nr_choices < 0 or nr_candidates <= 0 or max_choices <= 0:
        m = ("invalid parameters not (%d < 0 or %d <= 0 or %d <= 0)"
             % (nr_choices, nr_candidates, max_choices))
        raise ZeusError(m)

    if nr_choices > max_choices:
        m = ("Invalid number of choices (%d expected up to %d)" %
             (nr_choices, max_choices))
        raise AssertionError(m)

    return [nr_candidates, max_choices]

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

def vote_from_encoded(modulus, generator, order, public,
                      encoded, nr_candidates,total,
                      audit_code=None, publish=None):

	start = timer()
	alpha, beta, rnd = encrypt(encoded, modulus, generator, order, public)
	end=timer()
	print(end-start)
	total[0]+=end-start

    #proof = prove_encryption(modulus, generator, order, alpha, beta, rnd)
    #commitment, challenge, response = proof
	eb ={'modulus': modulus,'generator': generator,'order': order,'public': public,'alpha': alpha,'beta': beta}

   # fingerprint = numbers_hash((modulus, generator, alpha, beta,
    #                            commitment, challenge, response))
	vote = {'encrypted_ballot': eb}

    #if audit_code:
     #   vote['audit_code'] = audit_code

    #if publish:
     #   vote['voter_secret'] = rnd

	return vote

def get_random_selection(nr_elements, full=1):
    selection = []
    variable = not bool(full)
    append = selection.append
    for m in xrange(nr_elements, 1, -1):
        r = get_random_int(0, m+variable)
        if r == m:
            break
        append(r)
    else:
        append(0)
    return selection

#-----------------MAIN FUNCTION----------------------------
def mk_random_vote(self, selection=None, voter=None,
                             audit_code=None, publish=None):
		modulus, generator, order, public, secret = c2048()
		#public = self.do_get_election_public()
		#candidates = self.do_get_candidates()
		nr_candidates = 4
		s="---------------------"
		total= [1]
		total[0]=0.0

		for l in range(0,1000):
			print(s)
			selection=None
			if selection is None:
				#r = get_random_int(0, 4)
				#if r & 1:
				selection = get_random_selection(nr_candidates, full=0)
				print("random int is:" +str(selection))
				#else:
					#selection = get_random_party_selection(nr_candidates, 2)

			encoded = encode_selection(selection, nr_candidates)
	        #valid = True
			vote = vote_from_encoded(modulus, generator, order, public,
	                                 encoded, nr_candidates,total,
	                                 audit_code=0, publish=1)
        #rnd = vote['voter_secret']
        #if not publish:
            #del vote['voter_secret']
		print("total is :" + str(total))
		return vote, selection, encoded if valid else None, rnd

def main():
	mk_random_vote(None,None,None,None)

if __name__ == "__main__":
	main()