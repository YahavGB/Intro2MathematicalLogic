# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.semantics import *
from propositions.operators import *
from propositions.axiomatic_systems import *

######################################################################
#   Helpers
######################################################################


def proof_model_implies(formula: Formula, model: Model, builder: ProofBuilder):
    """
    Builds an implies claim of a model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.
        builder: The proof builder.
    """

    # Does our formula evaluates to true?
    if evaluate(formula, model):
        # Build the proof based on the LHS evaluation value
        if evaluate(formula.first, model):
            proof = prove_in_model(formula.second, model)
            implies = Proof.Line(Formula(FormulaToken.T_IMPLIES.value, formula.second, formula), I1, [])
        else:
            proof = prove_in_model(formula.first.inverse(), model)
            implies = Proof.Line(Formula(FormulaToken.T_IMPLIES.value, formula.first.inverse(), formula), I2, [])

        # Append
        builder.add_lines(proof.lines) \
            .add_line(implies) \
            .add_claim_line(formula, MP, (len(proof.lines) - 1, len(proof.lines)))
    else:
        # Proof first and ~second, and imply them together
        lhs = prove_in_model(formula.first, model)
        rhs = prove_in_model(formula.second.inverse(), model)

        # Append the lhs and the rhs proofs (rhs with shifting)
        builder.add_lines(lhs.lines).add_lines(rhs.lines, len(lhs.lines))

        # Build the implying claims that concat lhs with rhs
        sub_claim = Formula(FormulaToken.T_IMPLIES.value, formula.second.inverse(),
                            Formula(FormulaToken.T_IMPLIES.value, formula.first, formula.second).inverse())
        builder.add_claim_line(Formula(FormulaToken.T_IMPLIES.value, formula.first, sub_claim), NI, ()) \
            .add_claim_line(sub_claim, MP, (len(lhs.lines) - 1, len(lhs.lines) + len(rhs.lines))) \
            .add_claim_line(Formula(FormulaToken.T_IMPLIES.value, formula.first, formula.second).inverse(),
                            MP, (len(lhs.lines) + len(rhs.lines) - 1, len(lhs.lines) + len(rhs.lines) + 1))


def proof_model_negation(formula: Formula, model: Model, builder: ProofBuilder):
    """
    Builds a negation claim of a model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.
        builder: The proof builder.
    """
    # Proof the formula first token (we have root set as "~")
    main_proof = prove_in_model(formula.first, model)
    builder.add_lines(main_proof.lines)

    # If the evaluation of this formula is True, then we're done here.
    if evaluate(formula, model):
        return

    # We got a contradiction, so inverse the result
    lines_len = len(main_proof.lines)
    builder.add_claim_line(Formula(FormulaToken.T_IMPLIES.value, formula.first,
                                   formula.first.inverse().inverse()), NN, ()) \
        .add_claim_line(formula.first.inverse().inverse(), MP, (lines_len - 1, lines_len))


######################################################################
#   API
######################################################################

def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    return [Formula(v) if model.get(v) else Formula(v).inverse() for v in sorted(model.keys())]


def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)

    # Setup
    assumptions = formulae_capturing_model(model)
    builder = ProofBuilder()
    # Check if the formula is one of our assumptions
    if formula in assumptions:
        builder.add_assumption_line(formula)
    elif formula.inverse() in assumptions:
        builder.add_assumption_line(formula.inverse())
    elif formula.root == FormulaToken.T_IMPLIES.value:
        proof_model_implies(formula, model, builder)
    elif formula.root == FormulaToken.T_NOT.value:
        proof_model_negation(formula, model, builder)

    return builder.with_conclusion(InferenceRule(assumptions, builder.get_last_line().formula)) \
        .with_rules(AXIOMATIC_SYSTEM) \
        .build()


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules

    # Clean
    proof_from_affirmation = remove_assumption(proof_from_affirmation)
    proof_from_negation = remove_assumption(proof_from_negation)
    pfa_lines = len(proof_from_affirmation.lines)
    pfn_lines = len(proof_from_negation.lines)

    # Add both proof lines
    builder = ProofBuilder() \
        .add_lines(proof_from_affirmation.lines) \
        .add_lines(proof_from_negation.lines, len(proof_from_affirmation.lines))

    # Get the conclusion
    conclusion = proof_from_affirmation.lines[-1].formula
    negated_conclusion = proof_from_negation.lines[-1].formula

    # Imply the conclusions
    builder.add_claim_line(Formula(FormulaToken.T_IMPLIES.value,
                                   conclusion, Formula(FormulaToken.T_IMPLIES.value,
                                                       negated_conclusion, conclusion.second)), R, ()) \
        .add_claim_line(Formula(FormulaToken.T_IMPLIES.value, negated_conclusion, conclusion.second), MP,
                        (pfa_lines - 1, pfa_lines + pfn_lines)) \
        .add_claim_line(conclusion.second, MP, (pfa_lines + pfn_lines - 1, pfa_lines + pfn_lines + 1))

    return builder.with_conclusion(InferenceRule(
        proof_from_affirmation.statement.assumptions, builder.get_last_line().formula)) \
        .with_rules(proof_from_affirmation.rules.union([MP, I0, I1, D, R])) \
        .build()


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())

    # Does our formula has the exact same variables as the model?
    if len(tautology.variables().difference(model.keys())) < 1:
        # Can be easily proved using prove_in_model.
        return prove_in_model(tautology, model)

    # Test two proofs, one with the first model variables and one with the second
    all_variables = dict(zip(model.keys(), model.values()))

    # Get the variable that we're working on
    variable_key = sorted(tautology.variables())[len(model)]

    # First proof
    all_variables[variable_key] = True
    first_proof = prove_tautology(tautology, all_variables)

    # Second proof
    all_variables[variable_key] = False
    second_proof = prove_tautology(tautology, all_variables)
    return reduce_assumption(first_proof, second_proof)


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})

    for model in all_models(list(formula.variables())):
        if not evaluate(formula, model):
            return model

    return prove_tautology(formula, {})


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    if len(rule.assumptions) == 0:
        return rule.conclusion  # No assumptions so just using "q"

    # Assemble by loopin' backwards
    formula = rule.conclusion
    for i in range(len(rule.assumptions) - 1, -1, -1):
        formula = Formula(FormulaToken.T_IMPLIES.value, rule.assumptions[i], formula)

    return formula


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})

    # Creates a formula out of this rule
    formula = encode_as_formula(rule)

    # Prove it
    base_proof = prove_tautology(formula)

    # Build a new proof that contains, in addition to the base proof lines, the assumptions
    builder = ProofBuilder(rule) \
        .with_rules(AXIOMATIC_SYSTEM) \
        .add_lines(base_proof.lines)

    length = len(base_proof.lines)
    for assumption in rule.assumptions:
        builder.add_assumption_line(assumption) \
            .add_claim_line(formula.second, MP, (length, length - 1))
        formula = formula.second
        length += 2

    return builder.build()

def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})

    # Get all vars
    all_variables = list()
    for formula in formulae:
        all_variables += list(formula.variables())

    # Check if we got a formula that doesn't evaluate to true with one of the models
    for model in all_models(all_variables):
        if not any(True for f in formulae if not evaluate(f, model)):
            return model

    # Prove it using our axiomatic system
    return prove_sound_inference(InferenceRule(list(formulae),
                                               Formula(FormulaToken.T_IMPLIES.value,
                                                       Formula(FormulaTokenPlaceholder.T_SUBSTITUTION_LHS.value),
                                                       Formula(FormulaTokenPlaceholder.T_SUBSTITUTION_LHS.value))
                                               .inverse()))


def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
