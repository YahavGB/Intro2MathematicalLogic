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
    # Task 3.5
    substitution_map = {'<->': Formula.parse('~((p|q)&(~p|~q))'),
                        '-&': Formula.parse('~(p&q)'),
                        '-|': Formula.parse('~(p|q)'),
                        '->': Formula.parse('(~p|q)'),
                        'F': Formula.parse('(~p&p)'),
                        'T': Formula.parse('(~p|p)'),
                        '+': Formula.parse('((p|q)&(~p|~q))')}
    return formula.substitute_operators(substitution_map)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    substitution_map = {'|': Formula.parse('~(~p&~q)')}
    formula = to_not_and_or(formula)
    return formula.substitute_operators(substitution_map)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    substitution_map = {'&': Formula.parse('((p-&q)-&(p-&q))'),
                        '~': Formula.parse('(p-&p)')}
    formula = to_not_and(formula)
    return formula.substitute_operators(substitution_map)


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    substitution_map = {'&': Formula.parse('~(p->~q)')}
    formula = to_not_and(formula)
    return formula.substitute_operators(substitution_map)


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    substitution_map = {'~': Formula.parse('(p->F)')}
    formula = to_implies_not(formula)
    return formula.substitute_operators(substitution_map)