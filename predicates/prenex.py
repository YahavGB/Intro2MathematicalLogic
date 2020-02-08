# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
import sys

ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

############################################################
# Helpers
############################################################

BINARY_QUANTIFIER_REMOVAL_AXIOMS_MAPPING = {
    'lhs': {
        FormulaToken.T_QUALIFIER_EXISTS.value: {
            FormulaToken.T_AND.value: {
                'quantifier': FormulaToken.T_QUALIFIER_EXISTS.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[15],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[3]
            },
            FormulaToken.T_OR.value: {
                'quantifier': FormulaToken.T_QUALIFIER_EXISTS.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[15],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[7]
            },
            FormulaToken.T_IMPLIES.value: {
                'quantifier': FormulaToken.T_QUALIFIER_FORALL.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[14],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[11]
            },
        },
        FormulaToken.T_QUALIFIER_FORALL.value: {
            FormulaToken.T_AND.value: {
                'quantifier': FormulaToken.T_QUALIFIER_FORALL.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[14],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[2]
            },
            FormulaToken.T_OR.value: {
                'quantifier': FormulaToken.T_QUALIFIER_FORALL.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[14],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[6]
            },
            FormulaToken.T_IMPLIES.value: {
                'quantifier': FormulaToken.T_QUALIFIER_EXISTS.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[15],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[10]
            },
        },
    },
    'rhs': {
        FormulaToken.T_QUALIFIER_EXISTS.value: {
            FormulaToken.T_AND.value: {
                'quantifier': FormulaToken.T_QUALIFIER_EXISTS.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[15],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[5]
            },
            FormulaToken.T_OR.value: {
                'quantifier': FormulaToken.T_QUALIFIER_EXISTS.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[15],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[9]
            },
            FormulaToken.T_IMPLIES.value: {
                'quantifier': FormulaToken.T_QUALIFIER_EXISTS.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[15],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[13]
            },
        },
        FormulaToken.T_QUALIFIER_FORALL.value: {
            FormulaToken.T_AND.value: {
                'quantifier': FormulaToken.T_QUALIFIER_FORALL.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[14],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[4]
            },
            FormulaToken.T_OR.value: {
                'quantifier': FormulaToken.T_QUALIFIER_FORALL.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[14],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[8]
            },
            FormulaToken.T_IMPLIES.value: {
                'quantifier': FormulaToken.T_QUALIFIER_FORALL.value,
                'first_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[14],
                'second_axiom': ADDITIONAL_QUANTIFICATION_AXIOMS[12]
            },
        },
    }
}


def __do_uniquely_rename_quantified_variables(formula: Formula, forbidden_variables, prover: Prover) \
        -> Tuple[Formula, int]:
    """Actual Implementation :: Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    :param formula: The formula to work with.
    :param forbidden_variables: A set of forbidden variables.
    :param prover: The prover to append the results to.
    :return: A tuple containing the new formula and the line number.
    """
    # Are we qualifier-free?
    if is_quantifier_free(formula):
        # Just use this same formula. Easy, right?
        return formula, prover.add_tautology(equivalence_of(formula, formula))

    # Our tree root contains a qualifier?
    if formula.get_type() is Formula.FormulaType.T_QUALIFIER:
        # Expand
        new_formula, line = __do_uniquely_rename_quantified_variables(formula.predicate, forbidden_variables, prover)

        # Which axiom do we use?
        if new_formula.root == FormulaToken.T_QUALIFIER_FORALL.value:
            axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        else:
            axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]

        # Setup the substitution map
        substitution_map = {
            "R": formula.predicate.substitute({formula.variable: Term.placeholder()}, set()),
            "Q": new_formula.substitute({formula.variable: Term.placeholder()}, set()),
            "x": formula.variable,
            "y": next(fresh_variable_name_generator)
        }

        substituted_formula = new_formula.substitute({formula.variable: Term(substitution_map['y'])}, set())

        # Create the implication assumption
        conditional_line = prover.add_instantiated_assumption(Formula.FormulaBuilder.implies(
            equivalence_of(formula.predicate, new_formula),
            equivalence_of(Formula(formula.root, formula.variable, formula.predicate),
                           Formula(formula.root, substitution_map['y'], substituted_formula))
        ), axiom, substitution_map)

        # Finalize
        finalized_line = prover.add_mp(prover.get_line(conditional_line).formula.second, line, conditional_line)
        return prover.get_line(-1).formula.first.second, finalized_line

    if formula.get_type() is Formula.FormulaType.T_UNARY:
        # Invoke
        new_formula, line = __do_uniquely_rename_quantified_variables(formula.first, forbidden_variables, prover)

        # Inverse the formula
        new_formula = new_formula.inverse()

        # Build
        line = prover.add_tautological_implication(equivalence_of(formula, new_formula), {line})
        return new_formula, line

    if formula.get_type() is Formula.FormulaType.T_BINARY:
        # Reclusive invocation
        lhs, lhs_line = __do_uniquely_rename_quantified_variables(formula.first, forbidden_variables, prover)
        rhs, rhs_line = __do_uniquely_rename_quantified_variables(formula.second, forbidden_variables, prover)

        # Build
        new_formula = Formula(formula.root, lhs, rhs)
        line = prover.add_tautological_implication(equivalence_of(formula, new_formula), {lhs_line, rhs_line})
        return new_formula, line


def __pull_out_quantifications_across_binary_operator(formula: Formula, lhs_is_primary: bool) -> \
        Tuple[Formula, Proof]:
    """
    This is the actual implementation of pull_out_quantifications_from_(left|right)_across_binary_operator.
    This implementation was generalized so that we can use it in both variations, as it's mostly the same.

    Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """

    # Setup
    if lhs_is_primary:
        primary_hs = formula.first
        secondary_hs = formula.second
    else:
        primary_hs = formula.second
        secondary_hs = formula.first

    # Do we got a quantifier free definition?
    if is_quantifier_free(primary_hs):
        prover = Prover(set(Prover.AXIOMS) | set(ADDITIONAL_QUANTIFICATION_AXIOMS))
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    # Resolve the axioms that we should use
    data = BINARY_QUANTIFIER_REMOVAL_AXIOMS_MAPPING['lhs' if lhs_is_primary else 'rhs'][primary_hs.root][formula.root]

    first_axiom = data['first_axiom']
    second_axiom = data['second_axiom']
    remapped_quantifier = data['quantifier']
    if lhs_is_primary:
        new_formula = Formula(formula.root, primary_hs.predicate, formula.second)
    else:
        new_formula = Formula(formula.root, formula.first, primary_hs.predicate)

    # Apply the removal in a recursive way
    new_conclusion, proof = __pull_out_quantifications_across_binary_operator(new_formula, lhs_is_primary)

    # Begin our proof
    prover = Prover(set(Prover.AXIOMS) | set(ADDITIONAL_QUANTIFICATION_AXIOMS))
    substitution_map = {
        'R': new_formula.substitute({primary_hs.variable: Term.placeholder()}),
        'Q': new_conclusion.substitute({primary_hs.variable: Term.placeholder()}),
        'x': primary_hs.variable,
        'y': primary_hs.variable
    }

    step1 = prover.add_proof(proof.conclusion, proof)
    step1_instance = first_axiom.instantiate(substitution_map)

    # Step 2 + Step 3
    step2 = prover.add_instantiated_assumption(step1_instance, first_axiom, substitution_map)
    step3 = prover.add_mp(step1_instance.second, step1, step2)

    substitution_map = {
        'R': primary_hs.predicate.substitute({primary_hs.variable: Term.placeholder()}),
        'Q': secondary_hs.substitute({primary_hs.variable: Term.placeholder()}),
        'x': primary_hs.variable
    }
    step3_instance = second_axiom.instantiate(substitution_map)

    # Finalize
    step4 = prover.add_instantiated_assumption(step3_instance, second_axiom, substitution_map)
    conclusion = Formula(remapped_quantifier, primary_hs.variable, new_conclusion)
    prover.add_tautological_implication(equivalence_of(formula, conclusion), {step3, step4})
    return conclusion, prover.qed()


def __compute_rhs_proof(left: Formula) -> Tuple[Formula, Proof]:
    """
    Computes the RHS proof of the left given formula.
    :param left: The left formula.
    :return: A tuple contains the conclusion and the proof.
    """
    # If we're not dealing with quantifier, we can just remove the qualifications from the formula
    if left.get_type() is not Formula.FormulaType.T_QUALIFIER:
        return pull_out_quantifications_from_right_across_binary_operator(left)

    # Apply it on the predicate
    temp_conclusion, temp_proof = __compute_rhs_proof(left.predicate)

    # Setup
    prover = Prover(set(Prover.AXIOMS) | set(ADDITIONAL_QUANTIFICATION_AXIOMS))
    rhs = Formula(left.root, left.variable, temp_conclusion)
    if left.root == FormulaToken.T_QUALIFIER_EXISTS.value:
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    else:
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
    substitution_map = {
        'R': left.predicate.substitute({left.variable: Term.placeholder()}),
        'Q': rhs.predicate.substitute({left.variable: Term.placeholder()}),
        'x': left.variable,
        'y': left.variable
    }
    axiom_instance = axiom.instantiate(substitution_map)

    # Compute
    step1 = prover.add_proof(temp_proof.conclusion, temp_proof)
    step2 = prover.add_instantiated_assumption(axiom_instance, axiom, substitution_map)
    prover.add_mp(equivalence_of(left, rhs), step1, step2)
    right_proof = prover.qed()
    return rhs, right_proof

############################################################
# Public API (CS school Tasks)
############################################################


#: Additional axioms of quantification for first-order predicate logic.

def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    if formula.get_type() is Formula.FormulaType.T_BINARY:
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    if formula.get_type() is Formula.FormulaType.T_UNARY:
        return is_quantifier_free(formula.first)
    if formula.get_type() is Formula.FormulaType.T_QUALIFIER:
        return False
    if formula.get_type() is Formula.FormulaType.T_RELATION \
            or formula.get_type() is Formula.FormulaType.T_EQUALITY:
        return True


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    while formula is not None and not is_quantifier_free(formula):
        if not is_quantifier(formula.root):
            return False
        formula = formula.predicate

    return True


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Setup
    forbidden_variables = set(formula.free_variables())
    prover = Prover(set(Prover.AXIOMS) | set(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # Execute
    new_formula, line = __do_uniquely_rename_quantified_variables(formula, forbidden_variables, prover)

    # Finalize
    return new_formula, prover.qed()


def pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)

    # We don't have any quantifier?
    if is_quantifier_free(formula):
        prover = Prover(set(Prover.AXIOMS) | set(ADDITIONAL_QUANTIFICATION_AXIOMS))
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    # Which axioms do we use?
    if formula.first.root == FormulaToken.T_QUALIFIER_FORALL.value:
        quantifier = FormulaToken.T_QUALIFIER_EXISTS.value  # Switch the quantifier
        first_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[0]
        second_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    else:
        quantifier = FormulaToken.T_QUALIFIER_FORALL.value  # Switch the quantifier
        first_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[1]
        second_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]

    # Apply it recursively till we got quantifier-free expression
    conclusion_skeleton, proof = pull_out_quantifications_across_negation(formula.first.predicate.inverse())

    # Build the conclusion
    conclusion = Formula(quantifier, formula.first.variable, conclusion_skeleton)
    temp = equivalence_of(formula, conclusion)
    prover = Prover(set(Prover.AXIOMS) | set(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # First step
    step1 = prover.add_proof(proof.conclusion, proof)
    substitution_map = {
        'R': formula.first.predicate.inverse().substitute({formula.first.variable: Term.placeholder()}),
        'Q': conclusion_skeleton.substitute({formula.first.variable: Term.placeholder()}),
        'x': formula.first.variable,
        'y': formula.first.variable
    }
    step1_instance = second_axiom.instantiate(substitution_map)

    # Step 2 + Step 3
    step2 = prover.add_instantiated_assumption(step1_instance, second_axiom, substitution_map)
    step3 = prover.add_mp(step1_instance.second, step1, step2)
    substitution_map = {
        'R': formula.first.predicate.substitute({formula.first.variable: Term.placeholder()}),
        'x': formula.first.variable
    }
    step2_instance = first_axiom.instantiate(substitution_map)

    # Finalize
    conclude_proof = prover.add_instantiated_assumption(step2_instance, first_axiom, substitution_map)
    prover.add_tautological_implication(temp, {step3, conclude_proof})
    return conclusion, prover.qed()



def pull_out_quantifications_from_left_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)

    return __pull_out_quantifications_across_binary_operator(formula, True)


def pull_out_quantifications_from_right_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)

    return __pull_out_quantifications_across_binary_operator(formula, False)


def pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)

    # Setup
    prover = Prover(set(Prover.AXIOMS) | set(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # Remove the quantifications from the lhs and rhs
    lhs, left_proof = pull_out_quantifications_from_left_across_binary_operator(formula)
    rhs, right_proof = __compute_rhs_proof(lhs)

    # Merge and commit
    step1 = prover.add_proof(left_proof.conclusion, left_proof)
    step2 = prover.add_proof(right_proof.conclusion, right_proof)
    prover.add_tautological_implication(equivalence_of(formula, rhs), {step1, step2})
    return rhs, prover.qed()


def to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)

    # Setup
    prover = Prover(set(Prover.AXIOMS) | set(ADDITIONAL_QUANTIFICATION_AXIOMS))
    formula_type = formula.get_type()

    # Which formula did we got?
    if formula_type is Formula.FormulaType.T_RELATION or formula_type is Formula.FormulaType.T_EQUALITY:
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    if formula_type is Formula.FormulaType.T_UNARY:
        # Convert to prenex
        lhs, lhs_proof = to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        converted_formula, converted_proof = pull_out_quantifications_across_negation(lhs.inverse())

        # Compute
        step1 = prover.add_proof(lhs_proof.conclusion, lhs_proof)
        step2 = prover.add_proof(converted_proof.conclusion, converted_proof)
        prover.add_tautological_implication(equivalence_of(formula, converted_formula), {step1, step2})
        return converted_formula, prover.qed()

    if formula_type is Formula.FormulaType.T_BINARY:
        # Compute the lhs and rhs prenex forms
        lhs, lhs_proof = to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        rhs, rhs_proof = to_prenex_normal_form_from_uniquely_named_variables(formula.second)
        converted_formula, converted_proof = pull_out_quantifications_across_binary_operator(Formula(formula.root, lhs, rhs))

        # Compute
        step1 = prover.add_proof(lhs_proof.conclusion, lhs_proof)
        step2 = prover.add_proof(rhs_proof.conclusion, rhs_proof)
        step3 = prover.add_proof(converted_proof.conclusion, converted_proof)
        prover.add_tautological_implication(equivalence_of(formula, converted_formula), {step1, step2, step3})
        return converted_formula, prover.qed()

    if formula_type is Formula.FormulaType.T_QUALIFIER:
        # Find out which axiom we should use
        if formula.root == FormulaToken.T_QUALIFIER_EXISTS.value:
            axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        else:
            axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]

        # Compute the prenex form
        predicate, predicate_proof = to_prenex_normal_form_from_uniquely_named_variables(formula.predicate)
        converted_formula = Formula(formula.root, formula.variable, predicate)
        substitution_map = {
            'R': formula.predicate.substitute({formula.variable: Term.placeholder()}),
            'Q': converted_formula.predicate.substitute({formula.variable: Term.placeholder()}),
            'x': formula.variable,
            'y': formula.variable
        }
        axiom_instance = axiom.instantiate(substitution_map)

        # Computes
        step1 = prover.add_proof(predicate_proof.conclusion, predicate_proof)
        step2 = prover.add_instantiated_assumption(axiom_instance, axiom, substitution_map)
        prover.add_mp(equivalence_of(formula, converted_formula), step1, step2)
        return converted_formula, prover.qed()


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Setup
    prover = Prover(set(Prover.AXIOMS) | set(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # Rename the quantified variables
    updated_formula, updated_proof = uniquely_rename_quantified_variables(formula)

    # First step
    step1 = prover.add_proof(updated_proof.conclusion, updated_proof)
    updated_formula, updated_proof = to_prenex_normal_form_from_uniquely_named_variables(updated_formula)

    # Second step
    step2 = prover.add_proof(updated_proof.conclusion, updated_proof)

    # Finalize
    prover.add_tautological_implication(equivalence_of(formula, updated_formula), {step1, step2})
    return updated_formula, prover.qed()

