# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/some_proofs_test.py

"""Tests for the propositions.some_proofs module."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.some_proofs import *
from .utils import test_inference_proof
from propositions.proofs_test import offending_line

def test_prove_and_commutativity(debug=True):
    __test_prove_inference(prove_and_commutativity,
                           InferenceRule([Formula.parse('(p&q)')],
                                         Formula.parse('(q&p)')),
                           {A_RULE, AE1_RULE, AE2_RULE}, debug)

def test_prove_I0(debug=False):
    __test_prove_inference(prove_I0, I0, {MP, I1, D}, debug)

def test_prove_hypothetical_syllogism(debug=False):
    __test_prove_inference(prove_hypothetical_syllogism, HS, {MP, I0, I1, D},
                           debug)

def test_prove_I2(debug=False):
    __test_prove_inference(prove_I2, I2, {MP,I0,I1,D,N}, debug)

def test_prove_NNE(debug=False):
    __test_prove_inference(prove_NNE, NNE, {MP,I0,I1,D,N}, debug)

def test_prove_NN(debug=False):
    __test_prove_inference(prove_NN, NN, {MP,I0,I1,D,N}, debug)

def test_prove_CP(debug=False):
    __test_prove_inference(prove_CP, CP, {MP,I0,I1,D,N}, debug)

def test_prove_NI(debug=False):
    __test_prove_inference(prove_NI, NI, {MP,I0,I1,D,N}, debug)

def test_prove_CM(debug=False):
    __test_prove_inference(prove_CM, CM, {MP,I0,I1,D,N}, debug)

def test_prove_R(debug=False):
    __test_prove_inference(prove_R, R, {MP,I0,I1,D,N}, debug)

def test_prove_N(debug=False):
    __test_prove_inference(prove_N, N, {MP,I0,I1,D,N_ALTERNATIVE}, debug)

def test_prove_NA1(debug=False):
    __test_prove_inference(prove_NA1, NA1, {MP,I0,I1,D,N,AE1}, debug)

def test_prove_NA2(debug=False):
    __test_prove_inference(prove_NA2, NA2, {MP,I0,I1,D,N,AE2}, debug)

def test_prove_NO(debug=False):
    __test_prove_inference(prove_NO, NO, {MP,I0,I1,D,N,OE}, debug)

def __test_prove_inference(prover, rule, rules, debug):
    return test_inference_proof(prover, rule, rules, debug)  # My own util
    if debug:
        print('Testing', prover.__qualname__)
    proof = prover()
    if proof.statement != rule:
        print('*' * 25)
        print('Error: proof.statement != rule')
        print('proof.statement: ', proof.statement)
        print('rule: ', rule)
        print('*' * 25)
    assert proof.statement == rule
    assert proof.rules.issubset(rules), \
           "got " + str(proof.rules) + ", expected " + str(rules)
    if not proof.is_valid() or not (proof):
        print('=' * 35)
        print("INVALID Proof:")
        print(proof)

        invalid_lines = []
        for line_number in range(0, len(proof.lines)):
            if not proof.is_line_valid(line_number):
                invalid_lines.append(line_number)
        if len(invalid_lines) > 0:
            print('')
        print('=' * 35)
        sys.exit(1)

    assert proof.is_valid(), offending_line(proof)
    print('='*35)
    print("VALID Proof:")
    print(proof)
    print('='*35)

def test_ex4(debug=False):
    test_prove_and_commutativity(debug)
    test_prove_I0(debug)

def test_ex5(debug=False):
    test_prove_hypothetical_syllogism(debug)

def test_ex6_opt(debug=False):
    test_prove_I2(debug)
    test_prove_NNE(debug)
    test_prove_NN(debug)
    test_prove_CP(debug)
    test_prove_NI(debug)
    test_prove_CM(debug)
    test_prove_R(debug)
    test_prove_N(debug)
    test_prove_NA1(debug)
    test_prove_NA2(debug)
    test_prove_NO(debug)

def test_all(debug=False):
    test_ex4(debug)
    test_ex5(debug)
    test_ex6_opt(debug)
