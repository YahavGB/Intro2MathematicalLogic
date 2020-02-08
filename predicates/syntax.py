# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/syntax.py

"""Syntactic handling of first-order formulas and terms."""

from __future__ import annotations
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union, List, Callable

from logic_utils import fresh_variable_name_generator, frozen
from copy import deepcopy
from enum import Enum, IntFlag

from propositions.syntax import Formula as PropositionalFormula, \
                                is_variable as is_propositional_variable

############################################################
# Term definitions
############################################################

class TermToken(Enum):
    """Describes the available tokens in terms."""
    T_LPAREN = '('
    T_RPAREN = ')'
    T_ARG_SEP = ','
    T_UNDERSCORE = '_'

class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context."""

    def __init__(self, variable_name: str) -> None:
        """Initializes a `ForbiddenVariableError` from its offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it was to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return  (((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd'))
             and s.isalnum()) or s == '_'

def is_variable(s: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()

def is_function(s: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()

@frozen
class Term:
    """An immutable first-order term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    type: TermType

    class TermType(IntFlag):
        """Defines the available term types."""
        T_FUNCTION = 1 << 1
        T_CONST = 1 << 2
        T_VARIABLE = 1 << 3

        M_FUNCTION = T_FUNCTION
        M_ARG = T_CONST | T_VARIABLE

    class TermBuilder:
        """Provides a Fluent-API builder-pattern for terms.

        Note: Yes. Design-wise we'd make different builder for function,
        as it has a different set of functions. But I'm writing this projects alone.
        I'm sad. And Lonely. Sob (No, lol). But seriously, I can't be too strict on this one, because of time issues."""
        root: str
        type: Term.TermType
        arguments: List[Term, ...]

        def __init__(self, root: str, type: Term.TermType) -> None:
            self.root = root
            self.arguments = list()
            self.type = type

        @staticmethod
        def function(name: str) -> Term.TermBuilder:
            """
            Builds a function.

            Parameters:
                name The function name.

            Returns:
                The builder instance.
            """
            assert is_function(name)
            return Term.TermBuilder(name, Term.TermType.T_FUNCTION)

        @staticmethod
        def variable(name: str) -> Term.TermBuilder:
            """
            Builds a variable.

            Parameters:
                name The function name.

            Returns:
                The builder instance.
            """
            assert is_variable(name)
            return Term.TermBuilder(name, Term.TermType.T_VARIABLE)

        @staticmethod
        def constant(name: str) -> Term.TermBuilder:
            """
            Builds a variable.

            Parameters:
                name The function name.

            Returns:
                The builder instance.
            """
            assert is_constant(name)
            return Term.TermBuilder(name, Term.TermType.T_CONST)

        def add_argument(self, arg: Term):
            """
            Adds a function argument.

            Parameters:
                arg The argument to add.

            Returns:
                The term builder instance.
            """
            self.arguments.append(arg)
            return self

        def add_arguments(self, args: Union[Tuple[Term, ...], List[Term, ...]]):
            """
            Adds a function argument.

            Parameters:
                arg The argument to add.

            Returns:
                The term builder instance.
            """
            self.arguments += list(args)
            return self

        def get_num_args(self):
            """
            Gets the number of arguments this builder currently appended.

            Returns:
                The number of function args.
            """
            return len(self.arguments)

        def build(self) -> Term:
            """
            Builds the term.

            Returns:
                The constructed term.
            """
            assert self.root is not None
            if self.type == Term.TermType.T_FUNCTION:
                return Term(self.root, tuple(self.arguments))
            return Term(self.root)

    def __init__(self, root: str,
                 arguments: Optional[Sequence[Term]] = None) -> None:
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root):
            assert arguments is None
            self.root = root
            self.type = Term.TermType.T_CONST
        elif is_variable(root):
            assert arguments is None
            self.root = root
            self.type = Term.TermType.T_VARIABLE
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.type = Term.TermType.T_FUNCTION
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0

    def get_type(self):
        """
        Gets the term type

        Returns:
            The term type.
        """

        return self.type

    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Is it a function or an argument?
        if self.type == Term.TermType.T_FUNCTION:
            return self.root + TermToken.T_LPAREN.value \
                   + TermToken.T_ARG_SEP.value.join([t.__repr__() for t in self.arguments]) + TermToken.T_RPAREN.value

        return self.root

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        if len(s) == 0:
            return (None, '')

        # Read the next token
        next_token = Term.extract_next_alphanumeric_underscore_token(s)
        if next_token is None or len(next_token) == 0:
            return (None, '')

        # What is this token?
        if is_variable(next_token) or is_constant(next_token):
            return Term(next_token), s[len(next_token):]
        elif s[0] == TermToken.T_UNDERSCORE.value:
            return Term(TermToken.T_UNDERSCORE.value), s[1:]
        elif not is_function(next_token):
            return (None, '')

        # This should be a function!
        builder = Term.TermBuilder.function(next_token)
        s = s[len(next_token):]
        if s[0] != TermToken.T_LPAREN.value:
            return (None, '')

        # Parse the arguments
        while len(s) > 0 and s[0] != TermToken.T_RPAREN.value:
            # Parse
            arg, s = Term.parse_prefix(s[1:])
            if arg is None:
                return (None, '')

            # Add this argument
            builder.add_argument(arg)

            # Did we got a comma?
            if s[0] == TermToken.T_RPAREN.value:
                break
            elif s[0] != TermToken.T_ARG_SEP.value:
                return None, ''  # Invalid, as we expect a closing parenthesis

        s = s[1:]

        # Did we got anythin'?
        if builder.get_num_args() < 1:
            return (None, '')

        return builder.build(), s

    @staticmethod
    def parse(s: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            s: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        return Term.parse_prefix(s)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        return self.__recursive_collect(Term.TermType.T_CONST)

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        return self.__recursive_collect(Term.TermType.T_VARIABLE)

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        return self.__recursive_collect(Term.TermType.T_FUNCTION)

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)

        # What is this term
        if self.type is Term.TermType.T_FUNCTION:
            # Create the same function, while substituting the the map in the function argument(s)
            return Term(self.root, [a.substitute(substitution_map, forbidden_variables) for a in self.arguments])

        # Is this the term we want to substitute?
        if self.root in substitution_map:
            # Search for invalid args
            invalid_variable = substitution_map[self.root].__forbidden_variable_lookup(forbidden_variables)
            if invalid_variable is not None:
                raise ForbiddenVariableError(invalid_variable)

            # Substitute
            return substitution_map[self.root]

        return self

    @staticmethod
    def placeholder():
        """
        Creates a placeholder term.
        :return: The placeholder term.
        """
        return Term(TermToken.T_UNDERSCORE.value)

    @staticmethod
    def extract_next_alphanumeric_underscore_token(s: str) -> Optional[str]:
        """
        Extracts the next alphanumeric or underscore token from the string.

        Parameters:
            s The string.

        Returns:
            A tuple of the extracted token.
        """

        i = 0
        while i < len(s):
            if ('a' <= s[i] <= 'z') or ('A' <= s[i] <= 'Z') or ('0' <= s[i] <= '9') or s[i] == '_':
                i += 1
            else:
                break
        return s[:i]

    @staticmethod
    def __get_str_prefixed_predefined_token(s: str) -> Union[TermToken, None]:
        """Search for a {@link TermToken} at the beginning of the given string.

        Parameters:
            s: string to search the token in.

        Returns:
            The token, or None if there's no token starting at s[0]."""
        predefined_tokens = [e for e in TermToken
                             if len(e.value) <= len(s) and e.value == s[0:len(e.value)]]

        if len(predefined_tokens) == 1:
            return predefined_tokens[0]

        return None

    def __forbidden_variable_lookup(self, forbidden_variables: AbstractSet[str] = frozenset()) -> Optional[str]:
        """
        Determines if the term can satisfy the given substitution request.

        Parameters:
            substitution_map The substitutions map.
            forbidden_variables The forbidden variables.

        Returns:
            The forbidden argument or None if there're no forbidden arguments.
        """
        # Functions
        if self.type is Term.TermType.T_FUNCTION:
            for argument in self.arguments:
                invalid_arg = argument.__forbidden_variable_lookup(forbidden_variables)
                if invalid_arg is not None:
                    return invalid_arg

        # Constants
        if self.root in forbidden_variables:
            return self.root
        return None

    def __recursive_collect(self, t) -> Union[Set[str], Set[Tuple[str, int]]]:
        """
        Recursive collect the given term type.
        
        Parameters:
            t The term type to collect.
        
        Returns:
            The collected data.
        """
        ret_value = set()
        # Should we collect that?
        if self.type == t:
            if t == Term.TermType.T_FUNCTION:  # Hand-rolled hack to support T_FUNCTION here too.
                ret_value.add((self.root, len(self.arguments)))
            else:
                ret_value.add(self.root)

        if self.type == Term.TermType.T_FUNCTION:
            for arg in self.arguments:
                ret_value |= arg.__recursive_collect(t)

        return ret_value

############################################################
# Formula defintions
############################################################

class FormulaToken(Enum):
    T_LPAREN = '('
    T_RPAREN = ')'
    T_ARG_SEP = ','
    T_QUALIFIER_LPAREN = '['
    T_QUALIFIER_RPAREN = ']'

    T_QUALIFIER_FORALL = 'A'
    T_QUALIFIER_EXISTS = 'E'

    T_AND = '&'
    T_OR = '|'
    T_IMPLIES = '->'
    T_NOT = '~'

    T_EQUAL = '='
    T_SAME = 'SAME'

    T_UNDERSCORE = '_'

    T_UNARY_OPS = [T_NOT]
    T_BINARY_OPS = [T_AND, T_OR, T_IMPLIES]

    @staticmethod
    def get_prefix_binary_op(s) -> str:
        """
        Gets the prefix binary operator.

        Parameters:
            s The string.

        Returns:
            The operator, or none if not applicable.
        """
        for op in FormulaToken.T_BINARY_OPS.value:
            if s.startswith(op):
                return op
        return None

def is_equality(s: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return s == FormulaToken.T_EQUAL.value

def is_relation(s: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()

def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s in FormulaToken.T_UNARY_OPS.value

def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return s in FormulaToken.T_BINARY_OPS.value

def is_quantifier(s: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return s == FormulaToken.T_QUALIFIER_FORALL.value or s == FormulaToken.T_QUALIFIER_EXISTS.value

@frozen
class Formula:
    """An immutable first-order formula in tree representation, composed from
    relation names applied to first-order terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """

    class FormulaType(Enum):
        T_EQUALITY = 0
        T_RELATION = 1
        T_UNARY = 2
        T_BINARY = 3
        T_QUALIFIER = 4

    class FormulaBuilder:
        """
        A static class that provides utility methods to create formulas.
        """
        @staticmethod
        def equality(lhs: Term, rhs: Term) -> Formula:
            """
            Gets an equality formula.

            Parameters:
                lhs The left argument.
                rhs The right argument.

            Returns:
                The formula.
            """
            assert lhs is not None, rhs is not None
            return Formula(FormulaToken.T_EQUAL.value, (lhs, rhs))

        @staticmethod
        def implies(q: Formula, p: Formula) -> Formula:
            """
            Gets an implication formula.

            Parameters:
                q The left argument.
                p The right argument.

            Returns:
                The formula.
            """
            return Formula.FormulaBuilder.binary_operator(FormulaToken.T_IMPLIES.value, q, p)

        @staticmethod
        def binary_operator(operator: str, lhs: Formula, rhs: Formula) -> Formula:
            """
            Gets an binary operator formula.

            Parameters:
                operator The operator.
                lhs The left argument.
                rhs The right argument.

            Returns:
                The formula.
            """
            assert is_binary(operator)
            return Formula(operator, lhs, rhs)

        @staticmethod
        def relation(name: str, arguments: Sequence[Term, ...]) -> Formula:
            """
            Gets an relation formula.

            Parameters:
                name The relation name.
                arguments Tuple of arguments

            Returns:
                The builder.
            """
            assert is_relation(name)
            return Formula(name, tuple(arguments))

        @staticmethod
        def same_relation(arguments: Sequence[Term, ...]) -> Formula:
            """
            Builds a SAME relation.

            Parameters:
                arguments Tuple of arguments.

            Returns:
                The relation.
            """
            return Formula.FormulaBuilder.relation(FormulaToken.T_SAME.value, arguments)

        @staticmethod
        def unary_operator(operator: str, formula: Formula) -> Formula:
            """
            Gets an unary operator formula.

            Parameters:
                operator The operator.
                formula The argument.

            Returns:
                The formula.
            """
            assert is_unary(operator)
            return Formula(operator, formula)

        @staticmethod
        def forall(variable: str, formula: Formula) -> Formula:
            """
            Gets a for-all qualified formula.

            Parameters:
                name The qualifier name.
                variable The variable.
                formula The formula in which the qualifier applied on.

            Returns:
                The qualifier formula.
            """
            return Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_FORALL.value, variable, formula)

        @staticmethod
        def exists(variable: str, formula: Formula) -> Formula:
            """
            Gets an exists qualified formula.

            Parameters:
                name The qualifier name.
                variable The variable.
                formula The formula in which the qualifier applied on.

            Returns:
                The qualifier formula.
            """
            return Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_EXISTS.value, variable, formula)

        @staticmethod
        def qualifier(qualifier: str, variable: str, formula: Formula) -> Formula:
            """
            Gets a qualifier formula.

            Parameters:
                name The qualifier name.
                variable The variable.
                formula The formula in which the qualifier applied on.

            Returns:
                The qualifier formula.
            """
            assert is_quantifier(qualifier)
            return Formula(qualifier, variable, formula)

    root: str
    type: Formula.FormulaType
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_predicate: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the the root, if
                the root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
                self.type = Formula.FormulaType.T_EQUALITY
            else:
                self.type = Formula.FormulaType.T_RELATION
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
            self.type = Formula.FormulaType.T_UNARY
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate
            self.type = Formula.FormulaType.T_BINARY
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate
            self.type = Formula.FormulaType.T_QUALIFIER

    def get_type(self):
        """
        Gets the formula type.
        Returns:
            The formula type.
        """
        return self.type

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        if self.type == Formula.FormulaType.T_BINARY:
            return FormulaToken.T_LPAREN.value + self.first.__repr__() \
                   + self.root + self.second.__repr__() + FormulaToken.T_RPAREN.value
        elif self.type == Formula.FormulaType.T_QUALIFIER:
            return self.root + self.variable \
                   + FormulaToken.T_QUALIFIER_LPAREN.value \
                   + self.predicate.__repr__() + FormulaToken.T_QUALIFIER_RPAREN.value
        elif self.type == Formula.FormulaType.T_UNARY:
            return self.root + self.first.__repr__()
        elif self.type == Formula.FormulaType.T_EQUALITY:
            return str(self.arguments[0]) + self.root + str(self.arguments[1])
        elif self.type == Formula.FormulaType.T_RELATION:
            return self.root \
                   + FormulaToken.T_LPAREN.value \
                   + FormulaToken.T_ARG_SEP.value.join([str(a) for a in self.arguments]) \
                   + FormulaToken.T_RPAREN.value

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """

        if len(s) < 1:
            return None, ''

        first_token = s[0]

        # Is this a qualifier?
        if is_quantifier(first_token):
            # Get the variable
            variable, s = Term.parse_prefix(s[1:])
            if variable is None or len(s) < 1 or s[0] != FormulaToken.T_QUALIFIER_LPAREN.value:
                return None, ''

            formula, s = Formula.parse_prefix(s[1:])
            if formula is None or len(s) < 1 or s[0] != FormulaToken.T_QUALIFIER_RPAREN.value:
                return None, ''

            return Formula.FormulaBuilder.qualifier(first_token, variable.root, formula), s[1:]
        elif s[0] == FormulaToken.T_LPAREN.value:
            # might be a binary operator - parse the lhs
            lhs, s = Formula.parse_prefix(s[1:])

            # Did we got a valid lhs?
            if lhs is None:
                return None, ''

            # What is the operator?
            op = FormulaToken.get_prefix_binary_op(s)
            if op is None:
                return None, ''

            s = s[len(op):]

            # Parse the rhs
            rhs, s = Formula.parse_prefix(s)
            if rhs is None:
                return None, ''

            return Formula.FormulaBuilder.binary_operator(op, lhs, rhs), s[1:]
        elif is_unary(first_token):
            # That's a unary operator for ya
            formula, s = Formula.parse_prefix(s[1:])
            if formula is None:
                return None, ''
            return Formula.FormulaBuilder.unary_operator(first_token, formula), s
        elif is_relation(first_token):
            # Get the relation name
            name = Term.extract_next_alphanumeric_underscore_token(s)
            args = list()
            if name is None or len(name) < 1:
                return None, ''

            s = s[len(name):]
            if len(s) < 2 or s[0] != FormulaToken.T_LPAREN.value:
                return None, ''
            s = s[1:]

            # Extract the args
            while len(s) > 0 and s[0] != FormulaToken.T_RPAREN.value:
                # Parse
                arg, s = Term.parse_prefix(s)
                if arg is None:
                    return None, ''

                # Append
                args.append(arg)

                # What did we got next?
                if s[0] == FormulaToken.T_RPAREN.value:
                    break
                elif s[0] == FormulaToken.T_ARG_SEP.value:
                    s = s[1:]
                else:
                    # Invalid
                    return None, ''

            return Formula.FormulaBuilder.relation(name, args), s[1:]

        # Should be an equal by default.
        lhs, s = Term.parse_prefix(s)
        if lhs is None:
            return None, ''

        # Do we have the equal token
        if len(s) < 1 or s[0] != FormulaToken.T_EQUAL.value:
            return None, ''

        rhs, s = Term.parse_prefix(s[1:])
        return Formula.FormulaBuilder.equality(lhs, rhs), s

    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        return Formula.parse_prefix(s)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        return self.__recursive_collect(Term.TermType.T_CONST, lambda t: t.constants())

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        return self.__recursive_collect(Term.TermType.T_VARIABLE, lambda t: t.variables())

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of all variable names used in the current formula not only
            within a scope of a quantification on those variable names.
        """
        if self.type is Formula.FormulaType.T_UNARY:
            return self.first.free_variables()
        elif self.type is Formula.FormulaType.T_BINARY:
            return self.first.free_variables() | self.second.free_variables()
        elif self.type is Formula.FormulaType.T_QUALIFIER:
            variables = self.predicate.free_variables()
            if self.variable in variables:
                variables.remove(self.variable)
            return variables
        elif self.type is Formula.FormulaType.T_EQUALITY:
            return self.arguments[0].variables() | self.arguments[1].variables()
        elif self.type is Formula.FormulaType.T_RELATION:
            variables = set()
            for argument in self.arguments:
                variables = variables | argument.variables()
            return variables

        assert False

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        return self.__recursive_collect(None, lambda t: t.functions())

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        ret_value = set()
        if self.type == Formula.FormulaType.T_RELATION:
            # Should we take this relation?
            if self.type == Formula.FormulaType.T_RELATION:
                ret_value.add((self.root, len(self.arguments)))
        elif self.type == Formula.FormulaType.T_UNARY:
            ret_value = self.first.relations()
        elif self.type == Formula.FormulaType.T_BINARY:
            ret_value = self.first.relations()
            ret_value |= self.second.relations()
        elif self.type == Formula.FormulaType.T_QUALIFIER:
            ret_value = self.predicate.relations()

        return ret_value

    def inverse(self):
        """
        Gets the inverse of this formula.

        Returns:
            The formula inverse (a.k.a., ~formula).
        """
        return Formula(FormulaToken.T_NOT.value, self)

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
                Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)

        # Handle constants and variables
        if is_constant(self.root) or is_variable(self.root):
            return self.substitute(substitution_map, forbidden_variables)

        # Equality statement
        if self.type is Formula.FormulaType.T_EQUALITY:
            # Parse the lhs and rhs individually
            lhs = self.arguments[0].substitute(substitution_map, forbidden_variables)
            rhs = self.arguments[1].substitute(substitution_map, forbidden_variables)
            return Formula(self.root, [lhs, rhs])

        # Unary expression?
        if self.type is Formula.FormulaType.T_UNARY:
            lhs = self.first.substitute(substitution_map, forbidden_variables)
            return Formula(self.root, lhs)

        # Binary expression?
        if self.type is Formula.FormulaType.T_BINARY:
            # Parse the operator lhs and rhs
            lhs = self.first.substitute(substitution_map, forbidden_variables)
            rhs = self.second.substitute(substitution_map, forbidden_variables)
            return Formula(self.root, lhs, rhs)

        if self.type is Formula.FormulaType.T_RELATION:
            # Parse the arguments individually
            return Formula(self.root, [a.substitute(substitution_map, forbidden_variables)
                                       for a in self.arguments])

        if self.type is Formula.FormulaType.T_QUALIFIER:
            # Create new substitution and forbidden variable data types, such that the substitution
            # map won't contain the variable, as we already replaced it, and the forbidden map will
            # contain this variable, as we disallow to use it from now on.
            if isinstance(forbidden_variables, dict):
                forbidden_variables = set(forbidden_variables.values())
            else:
                forbidden_variables = {self.variable}

            new_substitution_map = deepcopy(substitution_map)

            if self.variable in new_substitution_map:
                del new_substitution_map[self.variable]

            return Formula(self.root, self.variable,
                           self.predicate.substitute(new_substitution_map, forbidden_variables))


    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a map from each atomic
            propositional formula to the subformula for which it was
            substituted.
        """
        substitution_map = {}
        skeleton = self.__create_propositional_skeleton(substitution_map)
        skeleton = PropositionalFormula.parse(str(skeleton))
        return skeleton, {v.root: k for k, v in substitution_map.items()}

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a first-order formula from a propositional skeleton and a
        substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute.
            substitution_map: a map from each atomic propositional subformula
                of the given skeleton to a first-order formula.

        Returns:
            A first-order formula obtained from the given propositional skeleton
            by substituting each atomic propositional subformula with the formula
            mapped to it by the given map.
        """
        for key in substitution_map:
            assert is_propositional_variable(key)

        node_type = skeleton.getType()
        if node_type is PropositionalFormula.NodeType.T_UNARY_OP:
            # Parse the lhs
            lhs = Formula.from_propositional_skeleton(skeleton.first, substitution_map)
            return Formula(skeleton.root, lhs)
        elif node_type is PropositionalFormula.NodeType.T_BINARY_OP:
            # Parse the lhs and rhs
            lhs = Formula.from_propositional_skeleton(skeleton.first, substitution_map)
            rhs = Formula.from_propositional_skeleton(skeleton.second, substitution_map)
            return Formula(skeleton.root, lhs, rhs)
        elif node_type is PropositionalFormula.NodeType.T_VAR:
            # Return the substituted variable, if we got one
            if skeleton.root in substitution_map:
                return substitution_map[skeleton.root]

        # Use the original value
        return skeleton

    def __create_propositional_skeleton(self, substitution_map: Mapping[Formula, Term]) -> str:
        """
        Creates a propositional skeleton string from the given substitution map.

        Parameters:
            substitution_map: The substitutions map.

        Returns:
            A string that describes the built skeleton string.
        """
        formula_type = self.get_type()
        if formula_type is Formula.FormulaType.T_UNARY:
            # Evaluate the lhs
            lhs = self.first.__create_propositional_skeleton(substitution_map)
            return self.root + str(lhs)
        elif formula_type is Formula.FormulaType.T_BINARY:
            # Evaluate the LHS and RHS
            lhs = self.first.__create_propositional_skeleton(substitution_map)
            rhs = self.second.__create_propositional_skeleton(substitution_map)
            return FormulaToken.T_LPAREN.value + str(lhs) + self.root + str(rhs) + FormulaToken.T_RPAREN.value
        elif formula_type is Formula.FormulaType.T_QUALIFIER \
                or formula_type is Formula.FormulaType.T_EQUALITY \
                or formula_type is Formula.FormulaType.T_RELATION:
            # Should we substitute this?
            if self in substitution_map:
                return str(substitution_map[self])

            # Create a new term
            substitution_map[self] = Term(next(fresh_variable_name_generator))
            return str(substitution_map[self])

        return str(self)

    def __recursive_collect(self, t: Optional[Term.TermType],
                            collector: Callable[[Optional[Term]], Union[Set[str], Set[Tuple[str, int]]]]) \
            -> Union[Set[str], Set[Tuple[str, int]]]:
        """
        Recursive collect the given term type.

        Parameters:
            t The type that we collect.
            collector A lambda used to collect the data.

        Returns:
            The collected data.
        """
        ret_value = set()
        if self.type == Formula.FormulaType.T_EQUALITY or self.type == Formula.FormulaType.T_RELATION:
            for arg in self.arguments:
                ret_value |= collector(arg)
        elif self.type == Formula.FormulaType.T_UNARY:
            ret_value = collector(self.first)
        elif self.type == Formula.FormulaType.T_BINARY:
            ret_value = collector(self.first)
            ret_value |= collector(self.second)
        elif self.type == Formula.FormulaType.T_QUALIFIER:
            ret_value = collector(self.predicate)
            if t == Term.TermType.T_VARIABLE:
                ret_value.add(self.variable)

        return ret_value
