# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in predicate logic."""

from typing import Union
from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

############################################################
# Helpers
############################################################


def __build_implies_claim(p: Union[str, Formula], q: Union[str, Formula]) -> str:
    """
    Builds an implies claim from the given formulas.
    :param p: The lhs claim.
    :param q: The rhs claim.
    :return: The result string.
    """
    if not isinstance(p, str):
        p = str(p)
    if not isinstance(q, str):
        q = str(q)
    return FormulaToken.T_LPAREN.value + p + FormulaToken.T_IMPLIES.value + q + FormulaToken.T_RPAREN.value


def __build_forall_claim(variable: str, formula: Union[str, Formula]) -> str:
    """
    Builds a "forall" claim from the given variable and claim formula.
    :param variable: The variable.
    :param formula: The formula that should get satisfied.
    :return: The result string.
    """
    if not isinstance(formula, str):
        formula = str(formula)

    return "{0}{1}[{2}]".format(FormulaToken.T_QUALIFIER_FORALL.value, variable, formula)


############################################################
# Public API (The tasks to implement)
############################################################

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()

    # Setup
    assumptions = {schema for schema in proof.assumptions if schema.formula != assumption}
    prover = Prover(assumptions)
    line_numbers = {}

    for line_num, line in enumerate(proof.lines):
        if isinstance(line, Proof.TautologyLine):
            # As we deal with a tautological line, just create the implication
            line_numbers[line_num] = prover.add_tautology(Formula.FormulaBuilder.implies(assumption, line.formula))
        elif isinstance(line, Proof.MPLine):
            # Create a MP implication
            line_numbers[line_num] = prover.add_tautological_implication(
                Formula.FormulaBuilder.implies(assumption, line.formula),
                {line_numbers[line.antecedent_line_number], line_numbers[line.conditional_line_number]})
        elif isinstance(line, Proof.AssumptionLine):
            # Handle standard assumptions
            if line.formula == assumption:
                line_numbers[line_num] = prover.add_tautology(Formula.FormulaBuilder.implies(assumption, assumption))
            else:
                instance = prover.add_instantiated_assumption(line.formula, line.assumption, line.instantiation_map)
                line_numbers[line_num] = prover.add_tautological_implication(
                    Formula.FormulaBuilder.implies(assumption, line.formula), {instance})
        else:
            # Build a UG claim
            current_number = line_numbers[line.predicate_line_number]
            base_formula = Formula.FormulaBuilder.forall(line.formula.variable, Formula.FormulaBuilder.implies(
                    assumption, line.formula.predicate))
            step1 = prover.add_ug(base_formula, current_number)
            p = Formula.FormulaBuilder.implies(base_formula, Formula.FormulaBuilder.implies(assumption, line.formula))
            q = line.formula.predicate.substitute({line.formula.variable: Term.placeholder()})
            step2 = prover.add_instantiated_assumption(p, Prover.US,
                                                       {'Q': assumption,  'R': q, 'x': line.formula.variable})
            step3 = prover.add_mp(Formula.FormulaBuilder.implies(assumption, line.formula),
                                  step1, step2)
            line_numbers[line_num] = step3

    return prover.qed()

def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Return:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()

    # Remove the proof assumption while basing a fully-fledged proof on it
    proof = remove_assumption(proof, assumption)

    # Create a prover out of this proof assumptions
    prover = Prover(proof.assumptions)

    # Append
    step = prover.add_proof(proof.conclusion, proof)

    # Conclude
    prover.add_tautological_implication(assumption.inverse(), {step})
    return prover.qed()


