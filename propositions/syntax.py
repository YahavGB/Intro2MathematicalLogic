# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulae."""

from __future__ import annotations
from typing import Mapping, Optional, Set, Tuple, Union, Callable
from logic_utils import frozen
from enum import Enum

######################################################################
#   Parsing Definitions
######################################################################

class FormulaToken(Enum):
    """
    Describes the available formula token.
    """
    T_TRUE = 'T'
    T_FALSE = 'F'
    
    T_NOT = '~'

    T_AND = '&'
    T_OR = '|'
    T_IMPLIES = '->'
    T_XOR = '+'
    T_IFF = '<->'
    T_NAND = '-&'
    T_NOR = '-|'

    T_LPAREN = '('
    T_RPAREN = ')'

    
class FormulaTokenPlaceholder(Enum):
    T_SUBSTITUTION_LHS = 'p'
    T_SUBSTITUTION_RHS = 'q'

######################################################################
# Utilities
######################################################################
def is_variable(s: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return s == FormulaToken.T_TRUE.value or s == FormulaToken.T_FALSE.value

def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == FormulaToken.T_NOT.value

def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    ops = [FormulaToken.T_AND.value, FormulaToken.T_OR.value, FormulaToken.T_IMPLIES.value,
         FormulaToken.T_XOR.value,  FormulaToken.T_IFF.value, FormulaToken.T_NAND.value,
          FormulaToken.T_NOR.value]
    return s in ops

######################################################################
# The Formula definition
######################################################################
@frozen
class Formula:
    """An immutable propositional formula in tree representation.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """

    class NodeType(Enum):
        """
        The available formula types.
        """
        T_UNDEFINED = 0
        T_VAR = 1
        T_CONST = 2
        T_UNARY_OP = 3
        T_BINARY_OP = 4

        @staticmethod
        def from_token(token: str):
            """Attempts to convert the given token into its coressponding NodeType.

            Parameters:
                token: string to convert.

            Returns:
                The NodeType that coresponds to the token.
            """
            # token_type_to_map is a static function variable.
            # See: https://stackoverflow.com/a/27783657
            Formula.NodeType.from_token.token_to_type_map = getattr(Formula.NodeType.from_token, "token_to_type_map", dict({
                FormulaToken.T_TRUE.value: Formula.NodeType.T_CONST,
                FormulaToken.T_FALSE.value: Formula.NodeType.T_CONST,
                FormulaToken.T_NOT.value: Formula.NodeType.T_UNARY_OP,
                FormulaToken.T_AND.value: Formula.NodeType.T_BINARY_OP,
                FormulaToken.T_OR.value: Formula.NodeType.T_BINARY_OP,
                FormulaToken.T_IMPLIES.value: Formula.NodeType.T_BINARY_OP,
                FormulaToken.T_XOR.value: Formula.NodeType.T_BINARY_OP,
                FormulaToken.T_IFF.value: Formula.NodeType.T_BINARY_OP,
                FormulaToken.T_NAND.value: Formula.NodeType.T_BINARY_OP,
                FormulaToken.T_NOR.value: Formula.NodeType.T_BINARY_OP,
                
                # Unused
                FormulaToken.T_LPAREN.value: Formula.NodeType.T_UNDEFINED,
                FormulaToken.T_RPAREN.value: Formula.NodeType.T_UNDEFINED
            }))

            if token in Formula.NodeType.from_token.token_to_type_map: # O(1)
                return Formula.NodeType.from_token.token_to_type_map[token]
            return Formula.NodeType.T_UNDEFINED

    # region Class Variables

    root: str
    first: Optional[Formula]
    second: Optional[Formula]
    
    # endregion
    
    # region Ctor

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        # Resolve the arguments
        if is_variable(root):
            assert first is None and second is None
            self.root = root
            self.__type = Formula.NodeType.T_VAR
        elif is_constant(root):
            assert first is None and second is None
            self.root = root
            self.__type = Formula.NodeType.T_CONST
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
            self.__type = Formula.NodeType.T_UNARY_OP
        else:
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second
            self.__type = Formula.NodeType.T_BINARY_OP

        # Other
        self.__interpertation = None

    # endregion

    # region Magic Methods

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
            does not equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        if self.__type == Formula.NodeType.T_VAR or self.__type == Formula.NodeType.T_CONST:
            # self.first and self.second wasn't defined. We're only dealing with self.root
            return self.root
        elif self.__type == Formula.NodeType.T_UNARY_OP:
            # Only self.first was defined (for example, a negation of a formula)
            return "{}{}".format(self.root, self.first)

        # A binary operator (a OP b)
        return "({}{}{})".format(self.first, self.root, self.second)

    # endregion

    # region Public API

    def getType(self) -> Formula.NodeType:
        """
        Gets this formula type.
        
        Returns:
            The formula actual node type.
        """
        return self.__type

    def inverse(self):
        """
        Gets the inverse of this formula.

        Returns:
            The formula inverse (a.k.a., ~formula).
        """
        return Formula(FormulaToken.T_NOT.value, self)

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        if self.__type == Formula.NodeType.T_VAR: # Note that T_CONST **is not** a variable! It's an operator.
            return {self.root} # Only self.root was defined.
        elif self.__type == Formula.NodeType.T_UNARY_OP:
            return self.first.variables() # self.second wasn't defined, and self.first is a Formula (self.root is a unary op).
        elif self.__type == Formula.NodeType.T_BINARY_OP:
            # Both self.first and self.second are Formulas, while self.root is the binary op.
            return self.first.variables() | self.second.variables()
        
        return set() # An operator (T|F)

    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        if self.__type == Formula.NodeType.T_VAR:
            return set() # A variable doesn't contain any op.
        elif self.__type == Formula.NodeType.T_CONST:
            return {self.root} # A (T|F) constant, which should be treated as an op.
        elif self.__type == Formula.NodeType.T_UNARY_OP:
            return {self.root} | self.first.operators() # In this case, we got the unary op and self.first.
        return {self.root} | self.first.operators() | self.second.operators()
        
    @staticmethod
    def parse_prefix(s: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the first token of the string is a variable name (e.g.,
            ``'x12'``), then the parsed prefix will be that entire variable name
            (and not just a part of it, such as ``'x1'``). If no prefix of the
            given string is a valid standard string representation of a formula
            then returned pair should be of ``None`` and an error message, where
            the error message is a string with some human-readable content.
        """
        if len(s) == 0:
            return (None, '')

        # As we're working with deterministic language, we can navigate
        # ourselves just by looking at the beginning of:
        prefixed_token = Formula.__get_str_prefixed_predefined_token(s)
        if prefixed_token is not None:
            # Attempt to parse the formula from the predefined token
            formula = Formula.__parse_using_prefixed_token(s, prefixed_token)
            if formula is None:
                return (None, '')
            
            return (formula, s[len(str(formula)):]) # As we implemented __repl__, we know exactly from where to cut ${s} - from len(formula).
                
        # The input wasn't a token, thus it **should** be a variable (or an invalid input)
        variable = Formula.__read_variable_token(s)
        if variable is None:
            return (None, '') # Illegal input
        
        # This is a variable Formula
        return (Formula(variable), s[len(variable):])

    @staticmethod
    def is_formula(s: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            s: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        result = Formula.parse_prefix(s)
        return result[0] != None and result[1] == ''
        
    
    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(s), "\"{}\" (type: {}) is not a valid formula".format(s, type(s))
        return Formula.parse_prefix(s)[0]

# Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        if self.__type == Formula.NodeType.T_VAR or self.__type == Formula.NodeType.T_CONST:
            return str(self.root)
        elif self.__type == Formula.NodeType.T_UNARY_OP:
            # Only self.first was defined (for example, a negation of a formula)
            return "{}{}".format(self.root, self.first.polish())

        # A binary operator (a OP b)
        return "{}{}{}".format(self.root, self.first.polish(), self.second.polish())

    @staticmethod
    def parse_polish(s: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """

        res = Formula.__parse_prefix_polish(s)
        assert res[1] == '' # The exercise assumes that we won't get invalid strings. 
        return res[0]

# Tasks for Chapter 3

    def substitute_variables(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((p->p)|z)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)')})
            (((q&r)->(q&r))|z)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3

        def predicate(formula: Formula) -> bool:
            return formula.getType() == Formula.NodeType.T_VAR
        
        def callback(symbol, lhs, rhs, substituted_formula):
            return substituted_formula

        # Preform using our general substitution visitor
        return self.__perform_substitution(substitution_map, predicate, callback)

    def substitute_operators(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        
        def predicate(formula: Formula) -> bool:
            return formula.getType() == Formula.NodeType.T_UNARY_OP \
                    or formula.getType() == Formula.NodeType.T_BINARY_OP \
                    or formula.getType() == Formula.NodeType.T_CONST
        
        def callback(symbol, lhs, rhs, substituted_formula):
            # What is this formula?
            if symbol == Formula.NodeType.T_UNARY_OP:
                # Replace just the formula.first
                return substituted_formula.substitute_variables({
                    FormulaTokenPlaceholder.T_SUBSTITUTION_LHS.value: lhs
                })
            elif symbol == Formula.NodeType.T_BINARY_OP:
                # Replace just the formula.first
                return substituted_formula.substitute_variables({
                    FormulaTokenPlaceholder.T_SUBSTITUTION_LHS.value: lhs,
                    FormulaTokenPlaceholder.T_SUBSTITUTION_RHS.value: rhs
                })
            elif symbol == Formula.NodeType.T_CONST:
                return substituted_formula
            return None

        # Preform using our general substitution visitor
        return self.__perform_substitution(substitution_map, predicate, callback)

    # endregion

    #region Private Methods

    def __perform_substitution(self, substitution_map: Mapping[str, Formula],
        predicate: Callable[[Formula], bool], 
        substitution: Callable[[Formula.NodeType, Formula, Formula, Formula], Formula]) -> Formula:
        """Iterates on the Formula nodes tree and perform substitution based on the given predicate
        to the given substitution map.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.
            predicate: A predicate function that decide whether or not to substitute the given formula.
                This predicate accepts:
                1. The formula to check if we should replace or not.
                Return Value: True if try to search for the substitution symbol for the
                              given formula, false otherwise.
                do a substitution to this formula, based on the given substitution_map.
            substitution: A callback used to replace a formula with another formula.

        Returns:
            The resulting formula.
        """
        formula = self
        
        # Test if this predicate can be activated on the specific formula:
        if predicate(formula) is not None:
            # Try to search for the specific node
            if formula.root in substitution_map:
                # "Only operators originating in the current formula are substituted",
                # thus we need to compute the lhs (and, if applicable, rhs) and only then substitute,
                # so we won't replace formula parts that were made as part of the substitution.
                # Example:
                # <pre>
                #   Formula.parse("~(p&q)").substitute_operators({
                #       "~": Formula.parse("(p&p)"),
                #       "&": Formula.parse("(p-|q)") })) 
                # </pre>
                # equals "((p-|q)&(p-|q))", as we won't replace the inner &
                # See: https://moodle2.cs.huji.ac.il/nu19/mod/forum/discuss.php?d=7697
                lhs = None
                rhs = None
                if formula.getType() == Formula.NodeType.T_UNARY_OP:
                    lhs = formula.first.__perform_substitution(substitution_map, predicate, substitution)
                    # formula = Formula(formula.root, lhs)
                elif formula.getType() == Formula.NodeType.T_BINARY_OP:
                    lhs = formula.first.__perform_substitution(substitution_map, predicate, substitution)
                    rhs = formula.second.__perform_substitution(substitution_map, predicate, substitution)
                    # formula = Formula(formula.root, lhs, rhs)
                
                return substitution(formula.getType(), lhs, rhs, substitution_map[formula.root])
        
        # Forward to sub-nodes
        if formula.getType() == Formula.NodeType.T_UNARY_OP:
            lhs = formula.first.__perform_substitution(substitution_map, predicate, substitution)
            return Formula(formula.root, lhs)
        elif formula.getType() == Formula.NodeType.T_BINARY_OP:
            lhs = formula.first.__perform_substitution(substitution_map, predicate, substitution)
            rhs = formula.second.__perform_substitution(substitution_map, predicate, substitution)
            return Formula(formula.root, lhs, rhs)
        
        return formula
    
    @staticmethod
    def __get_str_prefixed_predefined_token(s: str) -> Union[FormulaToken, None]:
        """Search for a {@link FormulaToken} at the beginning of the given string.

        Parameters:
            s: string to search the token in.

        Returns:
            The token, or None if there's no token starting at s[0]."""
        predefined_tokens = [e for e in FormulaToken
            if len(e.value) <= len(s) and e.value == s[0:len(e.value)]] # Can produce only len == 0 or len == 1

        if len(predefined_tokens) == 1:
            return predefined_tokens[0]

        return None
    
    @staticmethod
    def __parse_using_prefixed_token(s: str, token: FormulaToken) -> Union[Formula, None]:
        """Parse the next token in the string, using the given prefixed token prefix.

        Parameters:
            s: string to parse.
            token: The prefixed token.

        Returns:
            The parsed Formula node, or None if the prefixed token can't form a valid Formula."""
       
        # Try to determine which node type is it
        node_type = Formula.NodeType.from_token(token.value)

        if node_type == Formula.NodeType.T_CONST:
            # This is a constant (T | F)
            return Formula(token.value)
        elif node_type == Formula.NodeType.T_UNARY_OP:
            # This is a unary operator, so need to nest here the expr that this unary op is being applied on
            expr = Formula.parse_prefix(s[len(token.value):]) # Could've write s[1:], but want to support more complex unary ops in the future...
            if expr[0] is None: # Could we read it?
                return None

            # Build a unary op formula
            return Formula(token.value, expr[0])
        else:
            # We **expect** to get here an LPAREN to begin parenthesis parsing. If we got here RPAREN
            # or any other character - that's an invalid input.
            if token != FormulaToken.T_LPAREN:
                return None

            # This should be a binary operation, so firstly read the lhs
            pos = len(token.value)
            lhs = Formula.parse_prefix(s[pos:])
            if lhs[0] == None:
                return None
            pos += len(str(lhs[0]))

            # Do we have a valid binary operator?
            binary_op_token = Formula.__get_str_prefixed_predefined_token(s[pos:])
            if binary_op_token is None or Formula.NodeType.from_token(binary_op_token.value) != Formula.NodeType.T_BINARY_OP:
                # We got an illegal character (like "@", ";" etc.) or a FormulaToken which's not a binary op symbol. Both cases = error.
                return None
            
            pos += len(binary_op_token.value)
            # Finally, parse the rhs
            rhs = Formula.parse_prefix(s[pos:])
            if rhs[0] == None:
                return None

            # Make sure that we got an RPAREN after rhs
            rparen_token = Formula.__get_str_prefixed_predefined_token(rhs[1])
            if rparen_token != FormulaToken.T_RPAREN:
                return None
            
            # Done!
            return Formula(binary_op_token.value, lhs[0], rhs[0])

    @staticmethod
    def __read_variable_token(s: str) -> Union[str, None]:
        """Gets the variable token that sits at the beginning of the string, if it exists.

        Parameters:
            s: string to search the variable in.

        Returns:
            The variable, or None if there's no variable starting at s[0]."""
        if s[0] < 'p' or s[0] > 'z': # This is ASCII, so we **can** have s[0] > 'z'
            return None
        
        # Read the numbers, if any, that was associated with this variable.
        # Note that we don't care here if we have illegal character (like other character, special character etc.)
        # This is true thanks to the "Prefix-Free Property of Formulae".
        i = 1
        length = len(s)
        while i < length and s[i].isdigit():
            i += 1
        
        return s[0:i]

    @staticmethod
    def __parse_prefix_polish(s: str) -> Tuple[Union[Formula, None], str]:
        """Parses the polish-based prefix of the given string into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
        """
        if len(s) < 1:
            return None

        next_token = Formula.__get_str_prefixed_predefined_token(s)
        if next_token is not None:
            formula = Formula.__parse_polish_using_prefixed_token(s, next_token)
            if formula is None:
                return (None, '')
            return (formula, s[len(formula.polish()):])
        
        # The input wasn't a token, thus it **should** be a variable (or an invalid input)
        variable = Formula.__read_variable_token(s)
        if variable is None:
            return (None, '')
        return (Formula(variable), s[len(variable):])

    @staticmethod
    def __parse_polish_using_prefixed_token(s: str, token: FormulaToken) -> Union[Formula, None]:
        """Parse the next token in the given polish-based string, using the given prefixed token prefix.

        Parameters:
            s: string to parse.
            token: The prefixed token.

        Returns:
            The parsed Formula node, or None if the prefixed token can't form a valid Formula."""
       
        # Try to determine which node type is it
        node_type = Formula.NodeType.from_token(token.value)

        if node_type == Formula.NodeType.T_CONST:
            return Formula(token.value) # Constant
        elif node_type == Formula.NodeType.T_UNARY_OP:
            expr = Formula.__parse_prefix_polish(s[len(token.value):]) # Unary operator
            if expr[0] is None:
                return None
            return Formula(token.value, expr[0]) # Builds a unary op formula
        elif node_type == Formula.NodeType.T_BINARY_OP:
            # In polish form, the binary OP supplied at the beginning of the sub-formula,
            # so no need to look for parenthesis etc.
            lhs = Formula.__parse_prefix_polish(s[len(token.value):]) 
            if lhs is None:
                return None
            
            rhs = Formula.__parse_prefix_polish(lhs[1]) 
            if rhs is None:
                return None
            
            return Formula(token.value, lhs[0], rhs[0])
        else:
            assert False # We won't get here by the exercise assumptations...

    #endregion