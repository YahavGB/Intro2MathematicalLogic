# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *
import sys


############################################################
# Helpers
############################################################


def __handle_relation_function_symbols_replacement(formula: Formula) -> Formula:
    """
    Handle the replacement of function symbols inside a relation based formula.

    Parameters:
        formula The relation based formula (Formula Type = T_RELATION)

    Returns:
        The function-free formula that satisfies the original formula.
    """
    # Setup
    args = []
    relation_args = []

    # Parse every argument
    for argument in formula.arguments:
        # Are we dealing with a function term?
        if argument.get_type() == Term.TermType.T_FUNCTION:
            # Compile it
            function_free_term = compile_term(argument)

            # Use the variable as the new arg
            relation_args.append(function_free_term[-1].arguments[0])
            args += function_free_term
        else:
            relation_args.append(argument)

    # Build the new relation
    relation = Formula(formula.root, relation_args)

    # Replace
    to_return = __build_function_free_implication_relation(args, relation)
    return to_return


def __handle_equality_function_symbols_replacement(formula: Formula) -> Formula:
    """
     Handle the replacement of function symbols inside an equality/  based formula.

     Parameters:
         formula The relation based formula (Formula Type = T_RELATION)

     Returns:
         The function-free formula that satisfies the original formula.
     """
    # Setup (we assume that args[0] and arg[1] defined, as we got T_EQUALITY)
    lhs = formula.arguments[0]
    rhs = formula.arguments[1]

    if lhs.get_type() is not Term.TermType.T_FUNCTION:
        # Is the rhs a variable or constant as well?
        if rhs.get_type() is not Term.TermType.T_FUNCTION:
            # Nothing to do here.
            return formula

        # Process the rhs
        return __handle_one_sided_equality(rhs, lhs)
    else:
        # Is the rhs a variable or constant as well?
        if rhs.get_type() is not Term.TermType.T_FUNCTION:
            # Just process lhs
            return __handle_one_sided_equality(lhs, rhs)

        # Compile lhs and rhs
        compiled_lhs = compile_term(lhs)
        compiled_rhs = compile_term(rhs)

        # Build the end-goal relation
        relation = Formula.FormulaBuilder.equality(compiled_lhs[-1].arguments[0], compiled_rhs[-1].arguments[0])

        # Do we have any sub-implications to chain?
        if len(compiled_lhs) + len(compiled_rhs) == 1:
            return relation  # So we can just return the relation

        # Build the chain
        return __build_function_free_implication_relation(compiled_lhs + compiled_rhs, relation)


def __handle_one_sided_equality(primary: Term, secondary: Term) -> Formula:
    """
    Handle an equality formula in which the primary is a function term and the secondary isn't.

    Parameters:
        primary The function term.
        secondary The non-function term.

    Returns:
        The function-free formula.
    """
    # Convert to relation name
    relation_name = function_name_to_relation_name(primary.root)

    # Compile the primary term
    compiled_term = compile_term(primary)

    # Handle the second term
    second_term = compiled_term[-1].arguments[-1].arguments[0]

    # Build the relation
    relation = Formula(relation_name, [secondary, second_term])

    if len(compiled_term) == 1:
        return relation

    return __build_function_free_implication_relation(compiled_term, relation)


def __build_function_free_implication_relation(formulas: List[Formula], relation: Formula) -> Formula:
    """
    Builds a function-free relation using an implication expression from the given relation and list of formulas.

    Parameters:
        formulas The formulas list to chain.
        relation The end goal relation.

    Return:
        The chained formula.
    """
    # Handle the inner equalities
    handled = [__handle_equality_function_symbols_replacement(f) for f in formulas]

    # Do we have any inner equalities to imply on?
    if len(handled) < 1:
        return relation

    # Reversely build the implication statement
    stmt = Formula.FormulaBuilder.binary_operator(FormulaToken.T_IMPLIES.value, handled[-1], relation)
    for i in range(len(handled) - 1, 0, -1):
        # For-All wrap it
        stmt = Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_FORALL.value,
                                                formulas[i].arguments[0].root, stmt)

        # Create the previous implication
        stmt = Formula.FormulaBuilder.binary_operator(FormulaToken.T_IMPLIES.value, handled[i - 1], stmt)

    # Wrap the first statement
    stmt = Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_FORALL.value,
                                            formulas[0].arguments[0].root, stmt)
    return stmt


def __build_SAME_based_single_formula(formula: Formula) -> Formula:
    """
    Builds a SAME relation based formula with the given formula.

    Parameters:
        formula The formula to construct the SAME-relation based formula from.

    Returns:
        The SAME-relation based constructed formula.
    """

    # Setup
    formula_type = formula.get_type()

    # Resolve
    if formula_type is Formula.FormulaType.T_EQUALITY:
        return Formula.FormulaBuilder.same_relation(formula.arguments)
    if formula_type is Formula.FormulaType.T_RELATION:
        return formula
    if formula_type is Formula.FormulaType.T_UNARY:
        return Formula(formula.root,
                       __build_SAME_based_single_formula(formula.first))
    elif formula_type is Formula.FormulaType.T_QUALIFIER:
        return Formula(formula.root, formula.variable,
                       __build_SAME_based_single_formula(formula.predicate))
    if formula_type is Formula.FormulaType.T_BINARY:
        return Formula(formula.root,
                       __build_SAME_based_single_formula(formula.first),
                       __build_SAME_based_single_formula(formula.second))


def __build_SAME_formula_relationships() -> Tuple[Formula, Formula, Formula]:
    """
    A utility function used to create the commutative, distibutive and reflexive Formula rules.

    Returns:
        A tuple containing the commutative, distibutive and reflexive Formulas.
    """

    # Generate placeholder terms
    x_placeholder = Term(next(fresh_variable_name_generator))
    y_placeholder = Term(next(fresh_variable_name_generator))
    z_placeholder = Term(next(fresh_variable_name_generator))

    # Commutative Rule
    commutative_formula = Formula.FormulaBuilder.qualifier(
        FormulaToken.T_QUALIFIER_FORALL.value, x_placeholder.root,
        Formula.FormulaBuilder.qualifier(
            FormulaToken.T_QUALIFIER_FORALL.value, y_placeholder.root,
            Formula.FormulaBuilder.implies(
                Formula.FormulaBuilder.same_relation([x_placeholder, y_placeholder]),
                Formula.FormulaBuilder.same_relation([y_placeholder, x_placeholder])
            )))

    # Distributive Rule
    distributive_formula = Formula.FormulaBuilder.qualifier(
        FormulaToken.T_QUALIFIER_FORALL.value, z_placeholder.root, Formula.FormulaBuilder.qualifier(
            FormulaToken.T_QUALIFIER_FORALL.value, x_placeholder.root, Formula.FormulaBuilder.qualifier(
                FormulaToken.T_QUALIFIER_FORALL.value, y_placeholder.root,
                Formula.FormulaBuilder.implies(
                    Formula.FormulaBuilder.binary_operator(FormulaToken.T_AND.value,
                                                           Formula.FormulaBuilder.same_relation(
                                                               [x_placeholder, y_placeholder]),
                                                           Formula.FormulaBuilder.same_relation(
                                                               [y_placeholder, z_placeholder])),
                    Formula.FormulaBuilder.same_relation([x_placeholder, z_placeholder])
                )
            )))

    # Reflexive rule
    reflexive_formula = Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_FORALL.value, x_placeholder.root,
                                                         Formula.FormulaBuilder.same_relation(
                                                             [x_placeholder, x_placeholder]))

    # Done.
    return commutative_formula, distributive_formula, reflexive_formula


def __replace_relation_equal_meaning(meanings, source, destination):
    """
    Replaces the relation source meaning with the destination meaning, when they're equal.

    Parameters:
        meanings The set of meanings to look at.
        source The source meaning to search for.
        destination The destination meaning to replace the source with.

    Returns:
        The new meanings set.
    """
    for meaning in meanings:
        # Check if the source definition is available in our relationships
        relation_indexes = [definition[i] for definition in meanings[meaning] for i in range(len(definition))]
        if source not in relation_indexes:
            continue

        new_meaning = list(meanings[meaning])
        for i in range(len(new_meaning)):
            if source not in new_meaning[i]:
                continue

            # Replace the source with the destination (see: https://stackoverflow.com/a/20161067 )
            item_index = new_meaning[i].index(source)
            new_meaning[i] = new_meaning[i][:item_index] + (destination,) + new_meaning[i][item_index+1:]
        meanings[meaning] = set(new_meaning)

    return meanings


############################################################
# Main Implementations
############################################################


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings

    # Copy the basic model definitions
    new_relations = {**model.relation_meanings}  # Copies

    for function in model.function_meanings:
        relation_name = function_name_to_relation_name(function)
        invocations = model.function_meanings[function]
        relation_mapping = set()
        for invocation in invocations:
            relation_mapping.add((invocations[invocation],) + invocation)
        new_relations[relation_name] = relation_mapping

    return Model(model.universe, model.constant_meanings, new_relations)

def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings

    # Restoration
    functions_definitions = {}
    reduced_relations = {**model.relation_meanings}
    for function in original_functions:
        relation_name = function_name_to_relation_name(function)
        relation_data = model.relation_meanings[relation_name]

        # First value in the tuple is "y", the rest are (x_1, ..., x_n)
        invocations = dict()
        for data_set in relation_data:
            # Make sure we're not re-defining an invocation
            if data_set[1:] in invocations:
                return None
            invocations[data_set[1:]] = data_set[0:1][0]

        # Must have at least 1 invocation variant
        if len(invocations) < 1:
            return None

        # Make sure that the invocations number is the same as the universe arity
        arg = next(iter(invocations))
        if len(invocations) != len(model.universe) ** len(arg):
            return None

        # Add the function
        functions_definitions[function] = invocations

        # Remove the relation, as we don't use it anymore
        del reduced_relations[relation_name]

    # We need to satisfy the equality: functions == universe * arity
    return Model(model.universe, model.constant_meanings, reduced_relations, functions_definitions)


def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)

    # Setup
    result = []

    # Firstly, bundle the arguments
    new_term = Term.TermBuilder.function(term.root)
    for argument in term.arguments:
        # If this is a non-function argument, append it as is
        if argument.get_type() is not Term.TermType.T_FUNCTION:
            new_term.add_argument(argument)
            continue

        # Compile
        result += compile_term(argument)

        # Add the substituted argument as a new argument
        new_term.add_argument(result[-1].arguments[0])

    # Get the temporary variable name
    temp_variable = next(fresh_variable_name_generator)

    # Build the substituted formula name
    substituted_formula = Formula.FormulaBuilder.equality(
        Term(temp_variable), new_term.build()
    )

    return result + [substituted_formula]

def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function,arity in formula.functions()}.intersection(
                    {relation for relation,arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'

    # What are we handling?
    formula_type = formula.get_type()

    if formula_type is Formula.FormulaType.T_EQUALITY:
        return __handle_equality_function_symbols_replacement(formula)
    if formula_type is Formula.FormulaType.T_RELATION:
        return __handle_relation_function_symbols_replacement(formula)
    if formula_type is Formula.FormulaType.T_UNARY:
        return replace_functions_with_relations_in_formula(formula.first).inverse()
    elif formula_type is Formula.FormulaType.T_QUALIFIER:
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))
    if formula_type is Formula.FormulaType.T_BINARY:
        return Formula(formula.root,
                       replace_functions_with_relations_in_formula(formula.first),
                       replace_functions_with_relations_in_formula(formula.second))

def replace_functions_with_relations_in_formulas(formulas:
                                                 AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function,arity in formula.functions()}
                           for formula in formulas]).intersection(
                               set.union(*[{relation for relation,arity in
                                            formula.relations()} for
                                           formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'

    # Setup
    result_formulas = set()
    created_relations = set()

    # Convert each formula to its functions-free variant
    for formula in formulas:
        ff_formula = replace_functions_with_relations_in_formula(formula)  # ff = Functions-Free, lol.
        if ff_formula is None:
            continue  # Skip on failed results

        # Collect the formula relations
        created_relations |= ff_formula.relations()

        # Remove from the set the relations that we originally had, so we will remain
        # only with the new relations.
        total_relations = formula.relations()
        while len(total_relations) > 0:
            created_relations.remove(total_relations.pop())

        # Append the formula
        result_formulas.add(ff_formula)

    # Now, we will create a new formula for each, newly created, relation
    for relation in created_relations:
        # Setup
        first_placeholder = next(fresh_variable_name_generator)
        second_placeholder = next(fresh_variable_name_generator)
        placeholders = [Term(next(fresh_variable_name_generator)) for _ in range(relation[1] - 1)]
        first_relation_formula = Formula(relation[0], [Term(first_placeholder)] + placeholders)

        # Builds the first formula
        first_formula = Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_EXISTS.value,
                                                         first_placeholder, first_relation_formula)

        # Build the implication formula from the first relation to the second placeholder
        implies_formula = Formula.FormulaBuilder.implies(
            Formula.FormulaBuilder.binary_operator(FormulaToken.T_AND.value,
                                                   first_relation_formula,
                                                   Formula(relation[0], [Term(second_placeholder)] + placeholders)),
            Formula.FormulaBuilder.equality(Term(second_placeholder), Term(first_placeholder)))

        # Build the second formula
        second_formula = Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_FORALL.value,
                                                          second_placeholder, implies_formula)

        # Map the built formulas with qualifiers
        for term in placeholders:
            first_formula = Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_FORALL.value,
                                                             term.root, first_formula)
            second_formula = Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_FORALL.value,
                                                              term.root, second_formula)

        result_formulas.add(first_formula)
        result_formulas.add(second_formula)

    # Done.
    return result_formulas

def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation,arity in formula.relations()}

    # Setup
    formulas_set = set()
    relations_set = set()

    # Convert each single formula to a SAME formula based.
    for formula in formulas:
        formulas_set.add(__build_SAME_based_single_formula(formula))
        relations_set |= formula.relations()

    # Setup the relations implications
    for relation in relations_set:
        # Check the arity
        if relation[1] == 0:
            continue

        # Setup variable placeholders for the relations
        first_placeholders = [Term(next(fresh_variable_name_generator)) for _ in range(relation[1])]
        second_placeholders = [Term(next(fresh_variable_name_generator)) for _ in range(relation[1])]

        # Setup the equality formula
        equality_formula = Formula.FormulaBuilder.same_relation([first_placeholders[0], second_placeholders[0]])

        for i in range(1, relation[1]):
            equality_formula = Formula.FormulaBuilder.binary_operator(
                FormulaToken.T_AND.value, equality_formula,
                Formula.FormulaBuilder.same_relation([first_placeholders[i], second_placeholders[i]]))

        equality_formula = Formula.FormulaBuilder.implies(equality_formula,
                                                          Formula.FormulaBuilder.implies(
                                                              Formula(relation[0], first_placeholders),
                                                              Formula(relation[0], second_placeholders)))

        # Turn the equality formula into a FOR-ALL qualified formula,
        #  with the previously selected variables
        for placeholder in first_placeholders + second_placeholders:
            equality_formula = Formula.FormulaBuilder.qualifier(FormulaToken.T_QUALIFIER_FORALL.value,
                                                                placeholder.root, equality_formula)

        # Append
        formulas_set.add(equality_formula)

    # Build the commutative, distributive and reflexive formulas
    commutative_formula, distributive_formula, reflexive_formula = __build_SAME_formula_relationships()
    formulas_set.add(commutative_formula)
    formulas_set.add(distributive_formula)
    formulas_set.add(reflexive_formula)
    return formulas_set


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings

    # Use the previously defined relations meaning
    relation_meanings_set = {**model.relation_meanings}
    relation_meanings_set[FormulaToken.T_SAME.value] = set()  # Reset the SAME keyword meaning

    # Define reflexive associations for same (as 1=1, 53=53, pizza=pizza etc.)
    for value in model.universe:
        relation_meanings_set[FormulaToken.T_SAME.value].add((value, value))

    # Construct the new model
    return Model(model.universe, model.constant_meanings, relation_meanings_set, model.function_meanings)


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0

    # Setup
    new_universe = set(model.universe)
    new_constant_meaning = {**model.constant_meanings}
    new_function_meaning = {**model.function_meanings}
    new_relation_meaning = {**model.relation_meanings}

    # Iterate on the meanings defined for SAME
    for relation_definition in new_relation_meaning[FormulaToken.T_SAME.value]:
        # We got a different relation values for this SAME definition, but both are in the universe?
        if relation_definition[0] != relation_definition[1] and \
                (relation_definition[0] in new_universe and relation_definition[1] in new_universe):
            # Remove the old definition
            new_universe.remove(relation_definition[1])

            # Check if we need to re-define any constants
            for new_meaning in [m for m in new_constant_meaning.keys()
                                if new_constant_meaning[m] == relation_definition[1]]:
                new_constant_meaning[new_meaning] = relation_definition[0]

            # Setup the new function and relation meaning
            new_function_meaning = __replace_relation_equal_meaning(new_function_meaning,
                                                                    relation_definition[1],
                                                                    relation_definition[0])
            new_relation_meaning = __replace_relation_equal_meaning(new_relation_meaning,
                                                                    relation_definition[1],
                                                                    relation_definition[0])

    # Finalize
    del new_relation_meaning[FormulaToken.T_SAME.value]
    return Model(new_universe, new_constant_meaning, new_relation_meaning, new_function_meaning)
