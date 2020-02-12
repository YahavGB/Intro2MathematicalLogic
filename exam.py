#######################################################
# Helpers
#######################################################
from typing import List, Mapping, Set, Tuple

def print_result(value):
    print('='*35)
    print('RESULT:')
    print(value)
    print('='*35)

def print_error(msg):
    print('='*35)
    print('ERROR:')
    print(msg)
    print('='*35)


#######################################################
# Propositional
#######################################################

def propositional_to_prefix(formula: str):
    from propositions.syntax import Formula
    f = Formula.parse(formula)
    if f is None:
        print_error('Could not parse the given formula')
        return None

    print(f.polish())

def propositional_prove(formula: str, assumptions: List[str]):
    from propositions.syntax import Formula
    from propositions.tautology import proof_or_counterexample, prove_in_model, evaluate, all_models
    from propositions.tautology import prove_tautology, encode_as_formula
    from propositions.proofs import InferenceRule

    f = Formula.parse(formula)
    if f is None:
        print_error('Could not parse the given formula')
        return None

    collected_assumptions = []
    for assumption in assumptions:
        a = Formula.parse(assumption)
        if a is None:
            print_error('Could not parse the given assumption')
            return None
        collected_assumptions.append(a)

    f = encode_as_formula(InferenceRule(collected_assumptions, f))

    valid_proofs = []
    for model in all_models(list(f.variables())):
        if not evaluate(f, model):
            valid_proofs.append(prove_in_model(f, model))

    if len(valid_proofs) > 0:
        print_result('Found valid proof:\n' + str(valid_proofs))
        return True

    print_result('No valid proof.\n' + str(proof_or_counterexample(f)))
    return False

def propositional_is_consistent(formulas: List[str]):
    from propositions.syntax import Formula
    from propositions.tautology import all_models, evaluate
    from propositions.operators import to_implies_not

    formulas_list = []
    for f in formulas:
        f = Formula.parse(f)
        if f is None:
            print_error('Could not parse the given formula')
            return None
        f = to_implies_not(f)
        formulas_list.append(f)

    all_variables = list()
    for formula in formulas_list:
        all_variables += list(formula.variables())

    # Check if we got a formula that doesn't evaluate to true with one of the models
    for model in all_models(all_variables):
        if not any(True for f in formulas_list if not evaluate(f, model)):
            print_result(
                        'Formulas: ' + str(formulas) +
                        '\nThat is consistent! Model: ' + str(model))
            return True

    print_result(
                'Formulas: ' + str(formulas) +
                '\nThat is NOT consistent!')
    return False

def propositional_convert_to(formula: str, to: str):
    from propositions.syntax import Formula
    from propositions.operators import to_implies_false, to_implies_not, to_nand, to_not_and, to_not_and_or

    f = Formula.parse(formula)
    if f is None:
        print_error('Could not parse the given formula')
        return None

    to = to.lower().strip('to_')
    if to == 'implies_false':
        f = to_implies_false(f)
    elif to == 'implies_not':
        f = to_implies_not(f)
    elif to == 'nand':
        f = to_nand(f)
    elif to == 'not_and':
        f = to_not_and(f)
    elif to == 'not_and_or':
        f = to_not_and_or(f)
    else:
        print_error('Undefined action: ' + to + '. Allowed actions are: implies_false, implies_not, '
                                                'nand, not_and, not_and_or.')
        return False

    print_result(str(f))
    return True


#######################################################
# Predicates
#######################################################

def predicate_prenex_form(formula: str):
    from predicates.prenex import to_prenex_normal_form, is_in_prenex_normal_form
    from predicates.syntax import Formula
    f = Formula.parse(formula)
    if f is None:
        print_error('Could not parse the given formula')
        return None

    if is_in_prenex_normal_form(f):
        print_result('Original formula was already in prenex normal form.')
    else:
        print_result('Original formula wasnt in prenex normal form.'
                     '\nPrenex Normal Form: ' + str(to_prenex_normal_form(f)[0]))

def predicate_is_model(formula: str, world: Set[int], relations: Mapping[str, Set[Tuple]]):
    from predicates.prenex import to_prenex_normal_form
    from predicates.syntax import Formula
    from predicates.semantics import Model

    f = Formula.parse(formula)
    if f is None:
        print_error('Could not parse the given formula')
        return None

    m = Model(world, {str(k): k for k in world}, relations)
    print_result(m.is_model_of({f}))

def predicate_try_find_world(formula: str, relation: str, arity: int, max_item:int=4):
    from predicates.prenex import to_prenex_normal_form
    from predicates.syntax import Formula
    from predicates.semantics import Model
    from itertools import product, combinations
    f = Formula.parse(formula)
    if f is None:
        print_error('Could not parse the given formula')
        return None

    world = set(range(1, max_item))
    world_prod = set(product(world, repeat=arity))
    i = 1
    while i < 10:
        cbns = list(combinations(world_prod, i))
        if len(cbns) == 0:
            break
        i += 1

        for cbn in cbns:
            try:
                m = Model(world, {str(k): k for k in world}, {str(relation): set(cbn)})
                if m.is_model_of({f}):
                    print_result('Found Model!\nWorld: '+ str(world) + "\nModel: " + str(m))
                    return True
            except:
                pass
    print_error('Couldnt find model. Maybe we should try different args.')

def predicate_create_instance(schema_name: str, instantiation_map, destination_formula: str = None):
    from predicates.syntax import Formula
    from predicates.proofs import PROPOSITIONAL_AXIOM_TO_SCHEMA
    from predicates.prover import Prover
    consts = [name for name in vars(Prover) if not name.startswith('_')]
    if schema_name not in consts:
        print_error('Cant find the schema name.')
        return

    for key in instantiation_map:
        if isinstance(instantiation_map[key], str):
            instantiation_map[key] = Formula.parse(instantiation_map[key])

    schema = vars(Prover)[schema_name]
    result = [str(schema)]
    result.append('Instantiation Map: ' + str(instantiation_map))
    result.append('')

    instance = None
    try:
        # instantiation_map = {'Q': Formula.parse('Ax[Q(x)]')}
        instance = schema.instantiate(instantiation_map)
        result.append('Instance: ' + str(instance))
    except AssertionError:
        # raise
        result.append('ASSERT ERROR. CAN NOT GENERATE INSTANCE.')
        print_result('\n'.join(result))
        return

    if destination_formula is not None:
        destination_formula = Formula.parse(destination_formula)
        if destination_formula is None:
            print_error('Could not parse the given destination_formula')
            return None

        result.append('')
        result.append('Destination Formula: ' + str(destination_formula))
        result.append('')
        if destination_formula == instance:
            result.append('V! Formulas are equal.')
        else:
            result.append('X! Formulas ARE NOT equal.')
    print_result('\n'.join(result))

def predicate_handroll_proof():
    from predicates.syntax import Formula
    from predicates.proofs import Proof
    from predicates.prover import Prover

    #
    # #: Axiom schema of universal instantiation
    # UI = Schema(Formula.parse('(Ax[R(x)]->R(c))'), {'R', 'x', 'c'})
    # #: Axiom schema of existential introduction
    # EI = Schema(Formula.parse('(R(c)->Ex[R(x)])'), {'R', 'x', 'c'})
    # #: Axiom schema of universal simplification
    # US = Schema(Formula.parse('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))'),
    #             {'Q', 'R', 'x'})
    # #: Axiom schema of existential simplification
    # ES = Schema(Formula.parse('((Ax[(R(x)->Q())]&Ex[R(x)])->Q())'),
    #             {'Q', 'R', 'x'})
    # #: Axiom schema of reflexivity
    # RX = Schema(Formula.parse('c=c'), {'c'})
    # #: Axiom schema of meaning of equality
    # ME = Schema(Formula.parse('(c=d->(R(c)->R(d)))'), {'R', 'c', 'd'})
    # #: Axiomatic system for first-order predicate logic
    # AXIOMS = frozenset({UI, EI, US, ES, RX, ME})


    ###### Proof 1 #####
    # 1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    # 2. Aristotle is a man (``'Man(aristotle)'``)
    # the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    # prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'}, True)
    # step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    # step2 = prover.add_instantiated_assumption(
    #     '(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))',
    #     Prover.UI, {'R': '(Man(_)->Mortal(_))', 'c': 'aristotle'})
    # step3 = prover.add_mp('(Man(aristotle)->Mortal(aristotle))', step1, step2)
    # step4 = prover.add_assumption('Man(aristotle)')
    # step5 = prover.add_mp('Mortal(aristotle)', step4, step3)
    # print_result(str(prover.qed()))


    ###### Proof 2 #####
    prover = Prover({'Ax[(R(x)&Q(x))]'}, True)
    s0 = prover.add_assumption('Ax[(R(x)&Q(x))]')
    s1 = prover.add_instantiated_assumption('(Ax[(R(x)&Q(x))]->(R(x)&Q(x))', Prover.UI,
                                            { 'R': '(R(_)&Q(_))', 'c': 'x', 'x': 'x'})
    s2 = prover.add_mp('(R(x)&Q(x))', s0, s1)
    s3 = prover.add_tautology('((R(x)&Q(x))->R(x))')
    s4 = prover.add_mp('R(x)', s2, s3)
    s5 = prover.add_ug('Ax[R(x)]', s4)
    print_result(str(prover.qed()))

def predicate_get_primitives(formula: str):
    from predicates.syntax import Formula
    from predicates.completeness import get_primitives, get_constants
    f = Formula.parse(formula)
    if f is None:
        print_error('Could not parse the given formula')
        return None

    print_result('Formula: ' + str(f)
                 + '\nPrimitives: ' + str(get_primitives(f)))


#######################################################
# Main
#######################################################

# predicate_try_find_world('Ax[Ey[(G(x,y)&~G(y,x))]]','G',2)
# predicate_is_model('Ax[Ey[(G(x,y)&~G(y,x))]]',
#                    {1,2,3},
#                    {'G': {(3,1),(2,3),(1,2)}})
# predicate_handroll_proof()
# predicate_create_instance('ES', {'Q': 'Q()'}, '((Ax[(R(x)->Q())]&Ex[R(x)])->Q())')
predicate_get_primitives('(R(c1,d)|~(Q(c1)->~R(c2,a)))')
#
# def get_model(formula: str):
#     from predicates.prenex import to_prenex_normal_form
#     from predicates.completeness import model_or_inconsistency
#     from predicates.syntax import Formula
#     f = Formula.parse(formula)
#     if f is None:
#         print_error('Could not parse the given formula')
#         return None
#     prenex = to_prenex_normal_form(f)[0]
#     print_result(model_or_inconsistency({prenex}))
#
#
#
# def is_consistent(formula):
#     from predicates.prenex import to_prenex_normal_form
#     from predicates.completeness import model_or_inconsistency
#     from predicates.syntax import Formula
#
#     print(model_or_inconsistency({
#         Formula.parse('x'), Formula.parse('y'), Formula.parse('(x&y)')
#     }))


# get_model('Ax[Ey[(G(x,y)&~G(y,x))]]')