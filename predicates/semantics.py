# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/semantics.py

"""Semantic analysis of first-order logic constructs."""

from typing import AbstractSet, FrozenSet, Generic, Mapping, Tuple, TypeVar

from logic_utils import frozen, frozendict

from predicates.syntax import *
import itertools

#: A generic type for a universe element in a model.
T = TypeVar('T')

@frozen
class Model(Generic[T]):
    """An immutable model for first-order logic constructs.

    Attributes:
        universe (`~typing.FrozenSet`\\[`T`]): the set of elements to which
            terms can be evaluated and over which quantifications are defined.
        constant_meanings (`~typing.Mapping`\\[`str`, `T`]): mapping from each
            constant name to the universe element to which it evaluates.
        relation_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each relation name to the arity of the relation, or to ``-1`` if the
            relation is the empty relation.
        relation_meanings (`~typing.Mapping`\\[`str`, `~typing.AbstractSet`\\[`~typing.Tuple`\\[`T`, ...]]]):
            mapping from each n-ary relation name to argument n-tuples (of
            universe elements) for which the relation is true.
        function_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each function name to the arity of the function.
        function_meanings (`~typing.Mapping`\\[`str`, `~typing.Mapping`\\[`~typing.Tuple`\\[`T`, ...], `T`]]):
            mapping from each n-ary function name to the mapping from each
            argument n-tuple (of universe elements) to the universe element that
            the function outputs given these arguments.
    """
    universe: FrozenSet[T]
    constant_meanings: Mapping[str, T]
    relation_arities: Mapping[str, int]
    relation_meanings: Mapping[str, AbstractSet[Tuple[T, ...]]]
    function_arities: Mapping[str, int]
    function_meanings: Mapping[str, Mapping[Tuple[T, ...], T]]

    def __init__(self, universe: AbstractSet[T],
                 constant_meanings: Mapping[str, T],
                 relation_meanings: Mapping[str, AbstractSet[Tuple[T, ...]]],
                 function_meanings: Mapping[str, Mapping[Tuple[T, ...], T]] =
                 frozendict()) -> None:
        """Initializes a `Model` from its universe and constant, relation, and
        function meanings.

        Parameters:
            universe: the set of elements to which terms are to be evaluated
                and over which quantifications are to be defined.
            constant_meanings: mapping from each constant name to a universe
                element to which it is to be evaluated.
            relation_meanings: mapping from each relation name that is to
                be the name of an n-ary relation, to the argument n-tuples (of
                universe elements) for which the relation is to be true.
            function_meanings: mapping from each function name that is to
                be the name of an n-ary function, to a mapping from each
                argument n-tuple (of universe elements) to a universe element
                that the function is to output given these arguments.
        """
        self.universe = frozenset(universe)

        for constant in constant_meanings:
            assert is_constant(constant)
            assert constant_meanings[constant] in universe
        self.constant_meanings = frozendict(constant_meanings)

        relation_arities = {}
        for relation in relation_meanings:
            assert is_relation(relation)
            relation_meaning = relation_meanings[relation]
            if len(relation_meaning) == 0:
                arity = -1 # any
            else:
                some_arguments = next(iter(relation_meaning))
                arity = len(some_arguments)
                for arguments in relation_meaning:
                    assert len(arguments) == arity
                    for argument in arguments:
                        assert argument in universe
            relation_arities[relation] = arity
        self.relation_meanings = \
            frozendict({relation: frozenset(relation_meanings[relation]) for
                        relation in relation_meanings})
        self.relation_arities = frozendict(relation_arities)

        function_arities = {}
        for function in function_meanings:
            assert is_function(function)
            function_meaning = function_meanings[function]
            assert len(function_meaning) > 0
            some_argument = next(iter(function_meaning))
            arity = len(some_argument)
            assert arity > 0
            assert len(function_meaning) == len(universe)**arity
            for arguments in function_meaning:
                assert len(arguments) == arity
                for argument in arguments:
                    assert argument in universe
                assert function_meaning[arguments] in universe
            function_arities[function] = arity
        self.function_meanings = \
            frozendict({function: frozendict(function_meanings[function]) for
                        function in function_meanings})
        self.function_arities = frozendict(function_arities)

    def __repr__(self) -> str:
        """Computes a string representation of the current model.

        Returns:
            A string representation of the current model.
        """
        return 'Universe=' + str(self.universe) + '; Constant Meanings=' + \
               str(self.constant_meanings) + '; Relation Meanings=' + \
               str(self.relation_meanings) + \
               ('; Function Meanings=' + str(self.function_meanings)
                if len(self.function_meanings) > 0 else '')
        
    def evaluate_term(self, term: Term,
                      assignment: Mapping[str, T] = frozendict()) -> T:
        """Calculates the value of the given term in the current model, for the
        given assignment of values to variables names.

        Parameters:
            term: term to calculate the value of, for the constants and
                functions of which the current model has meanings.
            assignment: mapping from each variable name in the given term to a
                universe element to which it is to be evaluated.

        Returns:
            The value (in the universe of the current model) of the given
            term in the current model, for the given assignment of values to
            variable names.
        """
        assert term.constants().issubset(self.constant_meanings.keys())
        assert term.variables().issubset(assignment.keys())
        for function,arity in term.functions():
            assert function in self.function_meanings and \
                   self.function_arities[function] == arity
        # Decide based on the term type
        term_type = term.get_type()
        if term_type == Term.TermType.T_CONST:
            return self.constant_meanings[term.root]
        elif term_type == Term.TermType.T_VARIABLE:
            return assignment[term.root]
        elif term_type == Term.TermType.T_FUNCTION:
            # Evaluate the arguments
            args = [self.evaluate_term(t, assignment) for t in term.arguments]
            return self.function_meanings[term.root][tuple(args)]

    def assert_free_evaluate_formula(self, formula: Formula,
                                     assignment: Mapping[str, T] = frozendict()) -> bool:
        """Calculates the truth value of the given formula in the current model,
        for the given assignment of values to free occurrences of variables
        names.

        Parameters:
            formula: formula to calculate the truth value of, for the constants,
                functions, and relations of which the current model has
                meanings.
            assignment: mapping from each variable name that has a free
                occurrence in the given formula to a universe element to which
                it is to be evaluated.

        Returns:
            The truth value of the given formula in the current model, for the
            given assignment of values to free occurrences of variable names.
        """
        # As this method could be slow in long input, we won't use the get_type() semantic here.
        if is_equality(formula.root):
            return self.evaluate_term(formula.arguments[0], assignment) == self.evaluate_term(formula.arguments[1],
                                                                                              assignment)

        if is_relation(formula.root):
            if tuple(self.evaluate_term(value, assignment) for value in formula.arguments) \
                    not in self.relation_meanings[formula.root]:
                return False
            return True

        if is_unary(formula.root):
            return not self.assert_free_evaluate_formula(formula.first, assignment)
        if is_binary(formula.root):
            if formula.root == FormulaToken.T_AND.value:
                return self.assert_free_evaluate_formula(formula.first, assignment) and \
                       self.assert_free_evaluate_formula(formula.second, assignment)
            if formula.root == FormulaToken.T_OR.value:
                return self.assert_free_evaluate_formula(formula.first, assignment) or \
                       self.assert_free_evaluate_formula(formula.second, assignment)
            if formula.root == FormulaToken.T_IMPLIES.value:
                return self.assert_free_evaluate_formula(formula.second, assignment) if \
                    self.assert_free_evaluate_formula(formula.first, assignment) else True

        assignment = dict(assignment)
        if is_quantifier(formula.root):
            if formula.root == FormulaToken.T_QUALIFIER_FORALL.value:
                for i in self.universe:
                    if formula.variable in formula.predicate.free_variables():
                        assignment[formula.variable] = i
                    if not self.assert_free_evaluate_formula(formula.predicate, assignment):
                        return False
                    del assignment[formula.variable]
                return True
            else:
                for i in self.universe:
                    if formula.variable in formula.predicate.free_variables():
                        assignment[formula.variable] = i
                    if self.assert_free_evaluate_formula(formula.predicate, assignment):
                        return True
                    del assignment[formula.variable]
                return False

    def evaluate_formula(self, formula: Formula,
                         assignment: Mapping[str, T] = frozendict()) -> bool:
        """Calculates the truth value of the given formula in the current model,
        for the given assignment of values to free occurrences of variables
        names.

        Parameters:
            formula: formula to calculate the truth value of, for the constants,
                functions, and relations of which the current model has
                meanings.
            assignment: mapping from each variable name that has a free
                occurrence in the given formula to a universe element to which
                it is to be evaluated.

        Returns:
            The truth value of the given formula in the current model, for the
            given assignment of values to free occurrences of variable names.
        """
        assert formula.constants().issubset(self.constant_meanings.keys())
        assert formula.free_variables().issubset(assignment.keys())
        for function, arity in formula.functions():
            assert function in self.function_meanings and \
                   self.function_arities[function] == arity
        for relation, arity in formula.relations():
            assert relation in self.relation_meanings and \
                   self.relation_arities[relation] in {-1, arity}
        # Task 7.8
        return self.assert_free_evaluate_formula(formula, assignment)
        # if is_unary(formula.root):
        #     return not self.evaluate_formula(formula.first, assignment)
        # if is_binary(formula.root):
        #     if formula.root == "&":
        #         return self.evaluate_formula(formula.first, assignment) and self.evaluate_formula(formula.second,
        #                                                                                           assignment)
        #     if formula.root == "|":
        #         return self.evaluate_formula(formula.first, assignment) or self.evaluate_formula(formula.second,
        #                                                                                          assignment)
        #     if formula.root == "->":
        #         return self.evaluate_formula(formula.second, assignment) if self.evaluate_formula(formula.first,
        #                                                                                           assignment) else True
        # if is_equality(formula.root):
        #     return self.evaluate_term(formula.arguments[0], assignment) == self.evaluate_term(formula.arguments[1],
        #                                                                                       assignment)
        #
        # if is_relation(formula.root):
        #     if tuple(self.evaluate_term(value, assignment) for value in formula.arguments) not in \
        #             self.relation_meanings[formula.root]:
        #         return False
        #     return True
        # assignment = dict(assignment)
        # if is_quantifier(formula.root):
        #     if formula.root == "A":
        #         for i in self.universe:
        #             if formula.variable in formula.predicate.free_variables():
        #                 assignment[formula.variable] = i
        #             if not self.evaluate_formula(formula.predicate, assignment):
        #                 return False
        #             del assignment[formula.variable]
        #         return True
        #
        #     else:
        #         for i in self.universe:
        #             if formula.variable in formula.predicate.free_variables():
        #                 assignment[formula.variable] = i
        #             if self.evaluate_formula(formula.predicate, assignment):
        #                 return True
        #             del assignment[formula.variable]
        #         return False

    def is_model_of(self, formulas: AbstractSet[Formula]) -> bool:
        """Checks if the current model is a model for the given formulas.

        Returns:
            ``True`` if each of the given formulas evaluates to true in the
            current model for any assignment of elements from the universe of
            the current model to the free occurrences of variables in that
            formula, ``False`` otherwise.
        """
        for formula in formulas:
            assert formula.constants().issubset(self.constant_meanings.keys())
            for function,arity in formula.functions():
                assert function in self.function_meanings and \
                       self.function_arities[function] == arity
            for relation,arity in formula.relations():
                assert relation in self.relation_meanings and \
                       self.relation_arities[relation] in {-1, arity}

        for formula in formulas:
            # Get the permutations
            assignments = list(self.__all_models(formula.free_variables()))
            for assignment in assignments:
                if not self.evaluate_formula(formula, assignment):
                    return False

        return True

    def __all_models(self, variables: Set[str]) -> List[Mapping[str, T]]:
        """
        Gets the entire permutations of variables with values assigned from the universe.

        Parameters:
            variables The variables names.

        Returns:
            The permutations.
        """
        for combination in itertools.product(self.universe, repeat=len(variables)):
            yield dict(zip(variables, combination))  # Zip together with the variables
