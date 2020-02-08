# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/completeness.py

from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *
import itertools


def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants


def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)


def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation, is one of
        the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Setup
    constants = get_constants(sentences)
    visited = set()

    # Iterate on our sentences
    for sentence in sentences:
        # Skip on non-relational formulas (or formulas that we've already added)
        if sentence.get_type() is not Formula.FormulaType.T_RELATION \
                or sentence.root in visited:
            continue
        visited.add(sentence.root)

        # Take the product of this formula with the given constants as args
        for permutation in itertools.product(constants, repeat=len(sentence.arguments)):
            f = Formula(sentence.root, permutation)
            if not (f.inverse() in sentences or f in sentences):
                return False

    return True


def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0

    # Iterate throughout the sentences
    constants = get_constants(sentences)
    for sentence in sentences:
        if sentence.root == FormulaToken.T_QUALIFIER_FORALL.value:
            if any([True for c in constants
                    if sentence.predicate.substitute({sentence.variable: Term.parse(c)}) not in sentences]):
                return False

    return True


def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0

    # Iterate
    constants = get_constants(sentences)
    for sentence in sentences:
        # Is this an \exists stmt?
        if sentence.root == FormulaToken.T_QUALIFIER_EXISTS.value:
            if any([True for c in constants
                    if sentence.predicate.substitute({sentence.variable: Term.parse(c)}) in sentences]):
                # We could've find *something*!
                continue
            # Nothing relevant!
            return False

    return True


def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.

    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)

    # Setup
    constants = model.universe
    if is_quantifier_free(unsatisfied):
        return unsatisfied  # No need to go further

    if unsatisfied.root == FormulaToken.T_QUALIFIER_FORALL.value:
        for constant in constants:
            substitutions = unsatisfied.predicate.substitute({unsatisfied.variable: Term.parse(constant)})
            if not model.evaluate_formula(substitutions):
                return find_unsatisfied_quantifier_free_sentence(sentences, model, substitutions)
    elif unsatisfied.root == FormulaToken.T_QUALIFIER_EXISTS.value:
        for constant in constants:
            substitutions = unsatisfied.predicate.substitute({unsatisfied.variable: Term.parse(constant)})
            if substitutions in sentences:
                if not model.evaluate_formula(substitutions):
                    return find_unsatisfied_quantifier_free_sentence(sentences, model, substitutions)
    else:
        assert False


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)

    if quantifier_free.get_type() is Formula.FormulaType.T_BINARY:
        # A union of the formula lhs and rhs
        return get_primitives(quantifier_free.first) | get_primitives(quantifier_free.second)

    if quantifier_free.get_type() is Formula.FormulaType.T_UNARY:
        return get_primitives(quantifier_free.first)  # Just a unary lhs

    # Default case
    return {quantifier_free}


def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)

    # Initialize
    universe = {constant for constant in get_constants(sentences)}
    relation_meanings = {}
    constant_meanings = {str(constant): constant for constant in universe}

    # Iterate over our sentences
    for sentence in sentences:
        # Is this a relation?
        if sentence.get_type() is Formula.FormulaType.T_RELATION:
            # Turn it to be a list
            if sentence.root not in relation_meanings:
                relation_meanings[sentence.root] = list()

            # Append the data
            relation_meanings[sentence.root].append(tuple(str(arg) for arg in sentence.arguments))

    # Attempt to build the model
    result_model = Model(universe, constant_meanings, relation_meanings)
    if result_model.is_model_of(sentences):
        return result_model

    # We couldn't build a viable model, so let's build a contradiction
    contradiction_formula = ''
    for sentence in sentences:
        if not result_model.evaluate_formula(sentence):
            contradiction_formula = find_unsatisfied_quantifier_free_sentence(sentences, result_model, sentence)
            break

    primitives_set = set()
    for primitive in get_primitives(contradiction_formula):
        if primitive in sentences:
            primitives_set.add(primitive)
        else:
            primitives_set.add(primitive.inverse())

    # And finally - the prover
    prover = Prover(Prover.AXIOMS | primitives_set | {contradiction_formula})
    steps = [0 for _ in range(len(primitives_set))]
    for i, a in enumerate(primitives_set):
        steps[i] = prover.add_assumption(a)

    steps.append(prover.add_assumption(contradiction_formula))

    # The actual steps:
    step1 = prover.add_tautological_implication(contradiction_formula.inverse(), set(steps))
    step2 = prover.add_assumption(contradiction_formula)
    prover.add_tautological_implication(Formula.FormulaBuilder.binary_operator(FormulaToken.T_AND.value,
                                                                               contradiction_formula,
                                                                               contradiction_formula.inverse()),
                                        {step1, step2})
    return prover.qed()


def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(
        proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == \
           Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0

    # Create a prover from the intersection of the proofs assumptions
    prover = Prover(proof_from_affirmation.assumptions.intersection(proof_from_negation.assumptions))

    # Prove!
    proof_affirmation = proof_by_way_of_contradiction(proof_from_affirmation, affirmed_assumption.instantiate({}))
    proof_negation = proof_by_way_of_contradiction(proof_from_negation, negated_assumption.instantiate({}))

    # Get the contradiction end conclusion
    conclusion = Formula.FormulaBuilder.binary_operator(FormulaToken.T_AND.value,
                                                        proof_negation.conclusion, proof_affirmation.conclusion)
    step1 = prover.add_proof(proof_affirmation.conclusion, proof_affirmation)
    step2 = prover.add_proof(proof_negation.conclusion, proof_negation)
    prover.add_tautological_implication(conclusion, {step1, step2})
    return prover.qed()


def eliminate_universal_instantiation_assumption(proof: Proof, constant: str,
                                                 instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == \
           universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0

    # Create a prover without the given instantiations data
    prover = Prover(proof.assumptions - {Schema(instantiation)})

    # Proof by contradiction
    proof_by_contradiction = proof_by_way_of_contradiction(proof, instantiation)

    # The proof steps:
    step1 = prover.add_proof(proof_by_contradiction.conclusion, proof_by_contradiction)
    step2 = prover.add_assumption(universal)
    step3 = prover.add_universal_instantiation(instantiation, step2, term=list(instantiation.constants())[0])
    conclusion = Formula.FormulaBuilder.binary_operator(FormulaToken.T_AND.value,
                                                        instantiation, instantiation.inverse())

    # Finalize
    prover.add_tautological_implication(conclusion, {step1, step3})
    return prover.qed()


def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0

    constants = get_constants(sentences)
    augmented = set(sentences)
    for sentence in sentences:
        augmented |= {sentence.predicate.substitute({sentence.variable: Term.parse(c)})
                      for c in constants if sentence.root == FormulaToken.T_QUALIFIER_FORALL.value}
    return augmented


def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: a valid proof.
        constant: a constant name that does not appear as a template constant
            name in any of the assumptions of the given proof.
        variable: a variable name that does not appear anywhere in given the
            proof or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()

    # Setup
    substitution_map = {constant: Term.parse(variable)}
    assumptions_set = {}

    # Iterate on the proof assumptions and create a new template without these constants
    for assumption in proof.assumptions:
        template = set(assumption.templates)
        formula = assumption.formula.substitute(substitution_map)
        if constant in template:
            template = template - {constant}
            template = template | {variable}

        # Update the schema
        assumptions_set[assumption] = Schema(formula, template)

    # Create the prover
    prover = Prover(assumptions_set.values())
    for line in proof.lines:
        formula = line.formula.substitute(substitution_map)
        if isinstance(line, Proof.TautologyLine):
            prover.add_tautology(formula)
        elif isinstance(line, Proof.MPLine):
            prover.add_mp(formula, line.antecedent_line_number, line.conditional_line_number)
        elif isinstance(line, Proof.AssumptionLine):
            # In an assumption line, we need to update the instantiation map that we use
            instantiation_map = {}
            for key, value in line.instantiation_map.items():
                if not isinstance(value, str):
                    value = value.substitute(substitution_map)
                    value = str(value)
                else:
                    value = Term.parse(value)
                    value.substitute(substitution_map)
                    value = str(value)
                instantiation_map[key] = value

            prover.add_instantiated_assumption(formula, assumptions_set[line.assumption], instantiation_map)
        elif isinstance(line, Proof.UGLine):
            prover.add_ug(formula, line.predicate_line_number)

    return prover.qed()


def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()

    # Build a proof w/o the constants
    raw_proof = replace_constant(proof, constant)
    witness = witness.substitute({constant: Term.parse('zz')})

    # Create a proof by contradiction out of this raw proof
    proof_contradiction = proof_by_way_of_contradiction(raw_proof, witness)

    # Start to prove it:
    prover = Prover(proof_contradiction.assumptions)
    step1 = prover.add_proof(proof_contradiction.conclusion, proof_contradiction)
    proof_by_contradiction_conclusion = proof_contradiction.conclusion.substitute({'zz': Term.parse('x')})
    updated_conclusion = Formula.FormulaBuilder.binary_operator(FormulaToken.T_OR.value,
                                                                 proof_by_contradiction_conclusion,
                                                                 proof_by_contradiction_conclusion.inverse())
    step2 = prover.add_tautology(updated_conclusion)
    step3 = prover.add_free_instantiation(proof_by_contradiction_conclusion, step1, {'zz': Term.parse('x')})
    conclusion_implication = Formula.FormulaBuilder.implies(proof_by_contradiction_conclusion.first,
                                                            updated_conclusion.inverse())

    step4 = prover.add_tautological_implication(conclusion_implication, {step3})
    step5 = prover.add_ug(Formula.FormulaBuilder.forall('x', conclusion_implication), step4)

    substitution_map = {'Q': updated_conclusion.inverse(),
                        'R': existential.predicate.substitute({'x': Term.placeholder()})}
    es_instance = Prover.ES.instantiate(substitution_map)
    step6 = prover.add_instantiated_assumption(es_instance, Prover.ES, substitution_map)
    step7 = prover.add_tautological_implication(existential.inverse(), {step2, step5, step6})
    step8 = prover.add_assumption(existential)
    prover.add_tautological_implication(Formula.FormulaBuilder.binary_operator(FormulaToken.T_AND.value,
                                                                               existential.inverse(),
                                                                               existential), {step7, step8})
    return prover.qed()


def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0

    # Setup
    added_sentences = set()
    constants = get_constants(sentences)

    for sentence in sentences:
        # Skip on quantifier-free sentences
        if is_quantifier_free(sentence):
            continue

        # What is this sentence, anyway?
        if sentence.root == FormulaToken.T_QUALIFIER_EXISTS.value:
            variable = sentence.variable
            for cons in constants:
                if sentence.predicate.substitute({variable: Term(cons)}) in sentences:
                    break
            else:
                added_sentences.add(sentence.predicate.substitute({
                    variable: Term(next(fresh_constant_name_generator))
                }))

    # Finalize!
    return added_sentences | set(sentences)
