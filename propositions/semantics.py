# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, List, Mapping

from propositions.syntax import *
from propositions.proofs import *
import itertools

Model = Mapping[str, bool]


######################################################################
#   Helpers
######################################################################

def bool_to_symbol(value: bool) -> str:
    """Converts the given boolean value into a string symobl.

    Parameters:
        value: The boolean value.

    Returns:
        The symbol string that coresponds with the value boolean value.
    """
    if value:
        return FormulaToken.T_TRUE.value
    return FormulaToken.T_FALSE.value

def create_row_entry_str(symbol: str, truth_value: bool) -> str:
    """Creates a truth table row entry string for the given symbol and truth state.

    Parameters:
        symbol: A symbol (variable, formula) string.
        truth_value: The coresponding truth state to this symbol.

    Returns:
        The truth table row entry string for this pair.
    """
    truth_symbol = bool_to_symbol(truth_value)
    padding = ' ' * (len(symbol) - len(truth_symbol)) # Padding is in the length of the symbol, minus the truth symbol
    return ' {}{} '.format(truth_symbol, padding)

def create_dnf_component(model, truth_state):
    """Creates a DNF component for the given model.

    Parameters:
        model: The model.
        truth_state: Is this component should yield true or false.

    Returns:
        The DNF component.
    """
    if truth_state:
        return synthesize_for_model(model)
    return Formula(FormulaToken.T_NOT.value, synthesize_for_model(model))

def create_contradiction_formula(variable):
    model = {variable: True}
    formula = synthesize_for_model(model)
    return Formula(FormulaToken.T_AND.value,
        formula, Formula(FormulaToken.T_NOT.value, formula))

######################################################################
#   API
######################################################################

def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    
    # We already used Formula.NodeType to classify the formula based on its
    # tokens, so right now it's really simple to resolve the formula.

    def handleUndefined() -> bool:
        assert False # Can't do it using a lambda :(...

    def handleUnaryOp() -> bool:
        # Right now, we only have T_NOT
        return not evaluate(formula.first, model)

    def handleBinaryOp() -> bool:
        # Evaluate this expression based on the OP

        if formula.root == FormulaToken.T_AND.value:
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif formula.root == FormulaToken.T_OR.value:
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif formula.root == FormulaToken.T_IMPLIES.value:
            psi = evaluate(formula.first, model)
            xi = evaluate(formula.second, model)
            return not psi or (psi and xi) # The mathematical definition of implies. It appears with the same symbols in the book.
        elif formula.root == FormulaToken.T_XOR.value:
            psi = evaluate(formula.first, model)
            xi = evaluate(formula.second, model)
            return psi ^ xi # Just applying the built-in xor operator
        elif formula.root == FormulaToken.T_IFF.value:
            psi = evaluate(formula.first, model)
            xi = evaluate(formula.second, model)
            if psi:
                return xi
            else:
                return not xi
        elif formula.root == FormulaToken.T_NAND.value:
            psi = evaluate(formula.first, model)
            xi = evaluate(formula.second, model)
            return not (psi and xi)
        elif formula.root == FormulaToken.T_NOR.value:
            psi = evaluate(formula.first, model)
            xi = evaluate(formula.second, model)
            return (not psi) and (not xi) # Re-arraging De' Morgan rules to get NOR

        assert False # Undefined behavior. We shouldn't get here...

    resolvers = {
        Formula.NodeType.T_CONST: lambda: formula.root == FormulaToken.T_TRUE.value, # Available constants are only T_TRUE and T_FALSE
        Formula.NodeType.T_VAR: lambda: model[formula.root],
        Formula.NodeType.T_UNARY_OP: handleUnaryOp,
        Formula.NodeType.T_BINARY_OP: handleBinaryOp,

        Formula.NodeType.T_UNDEFINED: handleUndefined
    }

    # Get the correct resolver
    resolver = resolvers[formula.getType()]
    return resolver()

def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    for v in variables:
        assert is_variable(v)
    
    # Create a cartesian product of {True, False} x ... x {True, False} (repeated by the number of variables)
    for combination in itertools.product({True, False}, repeat=len(variables)):
        yield dict(zip(variables, combination)) # Zip together with the variables

def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    for model in models:
        yield evaluate(formula, model)

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Setup
    variables = list(formula.variables())

    # Sort the variables (as instructed, besides otherwise we might get
    # different results as set is un-ordered)
    # Must come before all_models!
    variables.sort()

    models = all_models(variables)
    formula_as_str = str(formula)
    headers = []
    rows = [ [] ]

    # We could build the table by printing the header (based on the variables + formula)
    # then the dividers (again, by another iteration) and lastly to iterate and print
    # each variable. This is quite un-efficient, though, isn't it? So what we'll do is to
    # collect the outputs in "headers" and "rows" and then batch print everything. Yahoo!
    
    # Headers
    for variable in list(variables) + [formula_as_str]:
        headers.append(' {} '.format(variable))
        rows[0].append('-' * (len(variable) + 2)) # +2 because of the spaces

    # Assemble the rows
    for model in models:
        row = [] # New row

        # Take each model
        for symbol, truth_value in model.items():
            row.append(create_row_entry_str(symbol, truth_value))
        
        # Calculate the result
        row.append(create_row_entry_str(formula_as_str, evaluate(formula, model)))

        # Append everything to the blueprint
        rows.append(row)

    # Now, print the headers
    print('|', end='')
    for header in headers:
        print(header + '|', end='')
    print('')

    # And the collected rows
    for row in rows:
        print('|', end='')
        for item in row:
            print(item + '|', end='')
        print('')


# The following three functions deals with the logical interpertation of a formula.
# We have 3 states:
# 1. Tautology: Iff every possible module produce a True result.
# 2. Satisfactory: Iff the formula is not contradiction and not a tautology <=> iff the negated function (~formula) not a tautology.
# 3. Contradiction: Iff the inverse formula (~formula) is a tautology.

def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    variables = formula.variables()
    models = all_models(variables)
    values = truth_values(formula, models)

    # Tautology: Every model will yield true.
    return all(value is True for value in values)

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Contradiction: The inverse formula is a tautology
    return is_tautology(formula.inverse())

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Satisfactory: The inverse formula is a NOT a tautology
    return not is_tautology(formula.inverse())

def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    def create_formula(variable, truth_state):
        if truth_state:
            return Formula(variable)
        return Formula(FormulaToken.T_NOT.value, Formula(variable))

    items = list(model.items())

    # Construct the initial formula
    if len(items) < 1:
        return None
    
    first_elem = items.pop(0) # Removing the first item
    formula = create_formula(first_elem[0], first_elem[1])

    # Handle the other elements using the conjunction operator
    for variable, truth_state in items:
        formula = Formula(FormulaToken.T_AND.value,
            formula, create_formula(variable, truth_state))

    return formula

def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0

    # Setup
    models = list(all_models(variables))

    # If the entire values is False, we should handle it explicitly.
    # Note that we're not allowed to return "F" formula.
    if all(value is False for value in values):
        # Creates a formula with (x & ~x) ∀x ∈ models
        # We can do it by just taking one model, as it'll contradict everything.
        formula = create_contradiction_formula(variables[0]) # First component
        for i in range(1, len(variables)): # Rest of them
            formula = Formula(FormulaToken.T_OR.value,
            formula, create_contradiction_formula(variables[i]))

        return formula
    
    # To create a DNF, we OR'ing the True models
    # Setup the first formula
    formula = None
    for i in range(len(models)):
        if not values[i]:
            continue

        if formula is None:
            formula = create_dnf_component(models[i], values[i])
        else:
            formula = Formula(FormulaToken.T_OR.value,
                formula, create_dnf_component(models[i], values[i]))

    return formula

# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.
    """
    assert is_model(model)

    for assumptions in rule.assumptions:
        if not evaluate(assumptions, model):
            return True

    return evaluate(rule.conclusion, model)

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    for model in all_models(rule.variables()):
        if not evaluate_inference(rule, model):
            return False
    return True
    