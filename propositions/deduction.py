# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)

    # Enter the base proof info
    implies_proof = ProofBuilder(InferenceRule(antecedent_proof.statement.assumptions, consequent)) \
        .with_rules(antecedent_proof.rules.union([conditional, MP]))

    # Add the antecedent proof lines
    implies_proof.add_lines(antecedent_proof.lines)

    # Compute the specialization map of the condition
    specialization_map = conditional.specialization_map(
        InferenceRule([], Formula(FormulaToken.T_IMPLIES.value, antecedent_proof.statement.conclusion, consequent)))

    # Write the consequence
    implies_proof.add_claim_line(conditional.conclusion.substitute_variables(specialization_map), conditional, ()) \
        .add_claim_line(consequent, MP, (len(antecedent_proof.lines) - 1, len(antecedent_proof.lines)))

    return implies_proof.build()

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)

    # Compute the specialization map of the double condition
    specialization_map = double_conditional.specialization_map(
        InferenceRule([], Formula(FormulaToken.T_IMPLIES.value, antecedent1_proof.statement.conclusion,
                                  Formula(FormulaToken.T_IMPLIES.value, antecedent2_proof.statement.conclusion,
                                          consequent))))

    # Prepare the proof
    double_implies_proof = ProofBuilder(InferenceRule(antecedent1_proof.statement.assumptions, consequent)) \
        .with_rules(antecedent1_proof.rules.union([double_conditional, MP]))

    # Add antecedent1
    double_implies_proof.add_lines(antecedent1_proof.lines)

    # Add antecedent2 while shifting up its assumptions indexes
    for line in antecedent2_proof.lines:
        if line.is_assumption():
            double_implies_proof.add_line(line)
        else:
            assumptions = tuple(map(lambda l: l + len(antecedent1_proof.lines), line.assumptions))
            double_implies_proof.add_claim_line(line.formula, line.rule, assumptions)

    # Write the double condition
    antecedent1_len = len(antecedent1_proof.lines)
    antecedent2_len = len(antecedent2_proof.lines)

    double_condition_formula = double_conditional.conclusion.substitute_variables(specialization_map)
    double_implies_proof.add_claim_line(double_condition_formula, double_conditional, ()) \
        .add_claim_line(double_condition_formula.second, MP, (antecedent1_len - 1, antecedent1_len + antecedent2_len)) \
        .add_claim_line(consequent, MP, (antecedent1_len + antecedent2_len - 1, antecedent1_len + antecedent2_len + 1))

    # Done.
    return double_implies_proof.build()


def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0

    # Setup
    last_assumption = proof.statement.assumptions[-1]
    shorter_proof = ProofBuilder(InferenceRule(proof.statement.assumptions[:-1],
                                 Formula(FormulaToken.T_IMPLIES.value, last_assumption, proof.statement.conclusion))) \
        .with_rules(proof.rules.union((D, MP, I0, I1)))

    # What is the last assumption?
    if last_assumption == proof.statement.conclusion:
        # We assuming the conclusion, thus we just need a simple implies here
        shorter_proof.add_claim_line(Formula(FormulaToken.T_IMPLIES.value, last_assumption, last_assumption), I0, ())
    elif proof.statement.conclusion in proof.statement.assumptions:
        # The proof conclusion is one of it's assumptions, but not the last one
        # so we need to navigate the assumption correctly with an implies argument.
        conclusion = proof.statement.conclusion
        assumption_implies_conclusion = Formula(FormulaToken.T_IMPLIES.value, last_assumption, conclusion)
        shorter_proof.add_assumption_line(conclusion) \
            .add_claim_line(Formula(FormulaToken.T_IMPLIES.value, conclusion, assumption_implies_conclusion), I1, []) \
            .add_claim_line(assumption_implies_conclusion, MP,
                            (shorter_proof.get_current_line() - 2, shorter_proof.get_current_line() - 1))
    elif proof.lines[-1].rule == MP:
        # We got an MP claim as a basis for the last line, so we have to
        # Recursively try to resolve the lines before it and after it
        # and then concat them together
        last_line = proof.lines[-1]
        assumption1 = last_line.assumptions[0]
        assumption2 = last_line.assumptions[1]

        proof1 = remove_assumption(Proof(InferenceRule(proof.statement.assumptions, proof.lines[assumption1].formula),
                                         proof.rules, proof.lines[:assumption1 + 1]))

        proof2 = remove_assumption(Proof(InferenceRule(proof.statement.assumptions, proof.lines[assumption2].formula),
                                         proof.rules, proof.lines[:assumption2 + 1]))

        # Add the first splitted proof
        shorter_proof.add_lines(proof1.lines)

        # Add the second splitted proof, while shifting the indexes of each line assumption
        for line in proof2.lines:
            if line.is_assumption():
                shorter_proof.add_line(line)
            else:
                shorter_proof.add_claim_line(line.formula, line.rule,
                                             tuple(map(lambda l: l + len(proof1.lines), line.assumptions)))

        # Create a claim that implies the lhs and rhs
        implies_claim = Formula(FormulaToken.T_IMPLIES.value,
                                Formula(FormulaToken.T_IMPLIES.value, last_assumption,
                                        Formula(FormulaToken.T_IMPLIES.value, proof.lines[assumption1].formula,
                                                proof.statement.conclusion)),
                                Formula(FormulaToken.T_IMPLIES.value,
                                        Formula(FormulaToken.T_IMPLIES.value, last_assumption,
                                                proof.lines[assumption1].formula),
                                        Formula(FormulaToken.T_IMPLIES.value, last_assumption,
                                                proof.statement.conclusion)))

        shorter_proof.add_claim_line(implies_claim, D, ()) \
            .add_claim_line(Formula(FormulaToken.T_IMPLIES.value,
                                    Formula(FormulaToken.T_IMPLIES.value, last_assumption, proof.lines[assumption1].formula),
                                    Formula(FormulaToken.T_IMPLIES.value, last_assumption, proof.statement.conclusion)),
                            MP, (len(proof1.lines) + len(proof2.lines) - 1, len(proof1.lines) + len(proof2.lines))) \
            .add_claim_line(Formula(FormulaToken.T_IMPLIES.value, last_assumption, proof.statement.conclusion),
                            MP, (len(proof1.lines) - 1, len(proof1.lines) + len(proof2.lines) + 1))
    else:
        # Connect the last rule and proof conclusion together
        rule = proof.lines[-1].rule
        conclusion = proof.statement.conclusion
        shorter_proof.add_claim_line(conclusion, rule, ()) \
            .add_claim_line(Formula(FormulaToken.T_IMPLIES.value, conclusion,
                                    Formula(FormulaToken.T_IMPLIES.value, last_assumption, conclusion)), I1, ()) \
            .add_claim_line(Formula(FormulaToken.T_IMPLIES.value, last_assumption, conclusion),
                            MP, (shorter_proof.get_current_line() - 2, shorter_proof.get_current_line() - 1))

    return shorter_proof.build()


def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules

    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)

def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0

    # Setup
    cleaned_proof = remove_assumption(proof)
    p = cleaned_proof.statement.conclusion.second.first
    q = cleaned_proof.statement.conclusion.first.first
    contradiction_proof = ProofBuilder(InferenceRule(cleaned_proof.statement.assumptions, q)) \
        .with_rules(cleaned_proof.rules.union([N]))

    # Append the standard proof lines
    contradiction_proof.add_lines(cleaned_proof.lines)

    # And finalize with the contradiction itself. Halmosh.
    contradiction_proof.add_claim_line(Formula(FormulaToken.T_IMPLIES.value, cleaned_proof.statement.conclusion,
                                               Formula(FormulaToken.T_IMPLIES.value, p, q)), N, ()) \
        .add_claim_line(Formula(FormulaToken.T_IMPLIES.value, p, q),
                        MP, (len(cleaned_proof.lines) - 1, len(cleaned_proof.lines))) \
        .add_claim_line(p, I0, ()) \
        # .add_claim_line(q, MP, (len(cleaned_proof.lines) + 2, len(cleaned_proof.lines) + 1))
    # 
    return contradiction_proof.build()
