# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulae to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    substitution_map = {
    #   Operator                        Replacement
        FormulaToken.T_TRUE.value:      "(p|~p)",
        FormulaToken.T_FALSE.value:     "(p&~p)",
        FormulaToken.T_IMPLIES.value:   "(~p|q)",
        FormulaToken.T_XOR.value:       "((p&~q)|(~p&q))",
        FormulaToken.T_IFF.value:       "((p&q)|(~p&~q))",
        FormulaToken.T_NAND.value:      "~(p&q)",
        FormulaToken.T_NOR.value:       "~(p|q)"
    }

    return formula.substitute_operators(dict((k, Formula.parse(v)) for k, v in substitution_map.items()))

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Define the substitution map. Note that we could've use the to_not_and_or
    # method before arriving here, but it seems like it might make things really slow.
    # We need to make it more efficient!
    substitution_map = {
    #   Operator                        Replacement
        FormulaToken.T_TRUE.value:      "~(p&~p)",
        FormulaToken.T_FALSE.value:     "(p&~p)",
        FormulaToken.T_IMPLIES.value:   "~(p&~q)",
        FormulaToken.T_XOR.value:       "(~(p&q)&~(~p&~q))",
        FormulaToken.T_IFF.value:       "(~(p&~q)&~(~p&q))",
        FormulaToken.T_NAND.value:      "~(p&q)",
        FormulaToken.T_NOR.value:       "(~p&~q)",
        FormulaToken.T_OR.value:        "~(~p&~q)",
    }
    
    return formula.substitute_operators(dict((k, Formula.parse(v)) for k, v in substitution_map.items()))


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """

    # Second conversation
    substitution_map = {
    #   Operator                        Replacement
        FormulaToken.T_TRUE.value:      "((p-&p)-&p)",
        FormulaToken.T_FALSE.value:     "(((p-&p)-&p)-&((p-&p)-&p))",
        FormulaToken.T_XOR.value:       "((p-&(p-&q))-&(q-&(p-&q)))",
        FormulaToken.T_IFF.value:       "((p-&q)-&((p-&p)-&(q-&q)))",
        FormulaToken.T_IMPLIES.value:   "(p-&(q-&q))",
        FormulaToken.T_NOR.value:       "(((p-&p)-&(q-&q))-&((p-&p)-&(q-&q)))",
        FormulaToken.T_OR.value:        "((p-&p)-&(q-&q))",
        FormulaToken.T_AND.value:       "((p-&q)-&(p-&q))",
        FormulaToken.T_NOT.value:       "(p-&p)",
    }

    return formula.substitute_operators(dict((k, Formula.parse(v)) for k, v in substitution_map.items()))


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # As it's not a standard gate, which makes it really hard to compose the actual
    # logical operators, I'll convert firstly to NAND, which's a universal gate
    # and covert in second trip this NAND operator to implies.
    formula = to_nand(formula)

    substitution_map = {
    #   Operator                        Replacement
        FormulaToken.T_NAND.value:      "(q->(p->~q))",
    }

    return formula.substitute_operators(dict((k, Formula.parse(v)) for k, v in substitution_map.items()))


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    formula = to_nand(formula)

    substitution_map = {
        #   Operator                        Replacement
        FormulaToken.T_NAND.value:      "(q->(p->F))",
    }

    return formula.substitute_operators(dict((k, Formula.parse(v)) for k, v in substitution_map.items()))
