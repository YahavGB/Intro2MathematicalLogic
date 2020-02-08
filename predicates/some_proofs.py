# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/some_proofs.py

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
# from predicates.deduction import *
# from predicates.prenex import equivalence_of

def syllogism_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_instantiated_assumption(
        '(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))',
        Prover.UI, {'R': '(Man(_)->Mortal(_))', 'c': 'aristotle'})
    step3 = prover.add_mp('(Man(aristotle)->Mortal(aristotle))', step1, step2)
    step4 = prover.add_assumption('Man(aristotle)')
    step5 = prover.add_mp('Mortal(aristotle)', step4, step3)
    return prover.qed()

def syllogism_proof_with_universal_instantiation(print_as_proof_forms: bool =
                                                 False) -> Proof:
    """Using the method `~predicates.prover.Prover.add_universal_instantiation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_universal_instantiation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_universal_instantiation(
        '(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
    step3 = prover.add_assumption('Man(aristotle)')
    step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
    return prover.qed()

def syllogism_all_all_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautology(
        '((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))')
    step6 = prover.add_mp(
        '((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))', step2, step5)
    step7 = prover.add_mp('(Greek(x)->Mortal(x))', step4, step6)
    step8 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step7)
    return prover.qed()

def syllogism_all_all_proof_with_tautological_implication(print_as_proof_forms:
                                                          bool = False) -> \
        Proof:
    """Using the method
    `~predicates.prover.Prover.add_tautological_implication`, proves from the
    assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_tautological_implication`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautological_implication(
        '(Greek(x)->Mortal(x))', {step2, step4})
    step6 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step5)
    return prover.qed()

def syllogism_all_exists_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI,
        {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_ug('Ax[(Man(x)->Ex[Mortal(x)])]', step5)
    step7 = prover.add_instantiated_assumption(
        '((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])', Prover.ES,
        {'R': 'Man(_)', 'Q': 'Ex[Mortal(x)]'})
    step8 = prover.add_tautological_implication(
        'Ex[Mortal(x)]', {step2, step6, step7})
    return prover.qed()

def syllogism_all_exists_proof_with_existential_derivation(print_as_proof_forms:
                                                           bool = False) -> \
        Proof:
    """Using the method `~predicates.prover.Prover.add_existential_derivation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_existential_derivation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI, {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_existential_derivation('Ex[Mortal(x)]', step2, step5)
    return prover.qed()

def lovers_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. Everybody loves somebody (``'Ax[Ey[Loves(x,y)]]'``), and
    2. Everybody loves a lover (``'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'``)
    
    the conclusion: Everybody loves everybody (``'Ax[Az[Loves(z,x)]]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    # Refactor to make it a bit more tidy
    ASSUMPTION_1 = 'Ax[Ey[Loves(x,y)]]'
    ASSUMPTION_2 = 'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'
    prover = Prover({ASSUMPTION_1, ASSUMPTION_2}, print_as_proof_forms)

    # First part
    assumption = prover.add_assumption(ASSUMPTION_2)
    step1 = prover.add_universal_instantiation( 'Az[Ay[(Loves(x,y)->Loves(z,x))]]', assumption, 'x')
    step2 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step1, 'z')
    step3 = prover.add_universal_instantiation('(Loves(x,y)->Loves(z,x))', step2, 'y')

    # Second part
    step4 = prover.add_assumption(ASSUMPTION_1)
    step5 = prover.add_universal_instantiation('Ey[Loves(x,y)]', step4, 'x')
    step6 = prover.add_existential_derivation('Loves(z,x)', step5, step3)

    # Conclusion
    step7 = prover.add_ug('Az[Loves(z,x)]', step6)
    prover.add_ug('Ax[Az[Loves(z,x)]]', step7)
    return prover.qed()

def homework_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. No homework is fun (``'~Ex[(Homework(x)&Fun(x))]'``), and
    2. Some reading is homework (``'Ex[(Homework(x)&Reading(x))]'``)
    
    the conclusion: Some reading is not fun (``'Ex[(Reading(x)&~Fun(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'}, print_as_proof_forms)

    # Inject the assumptions
    assumption_1 = prover.add_assumption("~Ex[(Homework(x)&Fun(x))]")
    assumption_2 = prover.add_assumption("Ex[(Homework(x)&Reading(x))]")

    # Reading is not fun -> there's a reading that's not fun.
    step1 = prover.add_instantiated_assumption("((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])", Prover.EI, {
        'R': "(Reading(_)&~Fun(_))",
        "x": "x",
        "c": "x"
    })

    # Homework is fun -> there's a fun homework
    step2 = prover.add_instantiated_assumption("((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])", Prover.EI, {
        'R': Formula.parse("(Homework(_)&Fun(_))"),
        "x": "x",
        "c": "x"
    })

    # There's no fun homework -> no (fun homework)
    step3 = prover.add_tautological_implication("(~Ex[(Homework(x)&Fun(x))]->~(Homework(x)&Fun(x)))", {
        assumption_1, step2
    })

    # There's no (homework is fun)
    my_argument = prover.add_mp("~(Homework(x)&Fun(x))", assumption_1, step3)

    # Conclude the implications
    implication1 = prover.add_tautological_implication("(Homework(x)->~Fun(x))", {my_argument})
    implication2 = prover.add_tautological_implication("((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))",
                                                       {implication1})

    main_conclusion = prover.add_tautological_implication("((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])",
                                                          {step1, implication2})
    prover.add_existential_derivation("Ex[(Reading(x)&~Fun(x))]", assumption_2, main_conclusion)

    return prover.qed()

#: The three group axioms
GROUP_AXIOMS = frozenset({'plus(0,x)=x', 'plus(minus(x),x)=0',
                          'plus(plus(x,y),z)=plus(x,plus(y,z))'})

def right_neutral_proof(stop_before_flipped_equality: bool,
                        stop_before_free_instantiation: bool,
                        stop_before_substituted_equality: bool,
                        stop_before_chained_equality: bool,
                        print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms that x+0=x (``'plus(x,0)=x'``).

    Parameters:
        stop_before_flipped_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_flipped_equality` and to return the
            prefix of the proof constructed up to that point.
        stop_before_free_instantiation: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_free_instantiation` and to return the
            prefix of the proof constructed up to that point.
        stop_before_substituted_equality: flag specifying stop proving just
            before the first call to
            `~predicates.prover.Prover.add_substituted_equality` and to return
            the prefix of the proof constructed up to that point.
        stop_before_chained_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_chained_equality` and to return the
            prefix of the proof constructed up to that point.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS, print_as_proof_forms)
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    associativity = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    if stop_before_flipped_equality:
        return prover.qed()
    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    flipped_negation = prover.add_flipped_equality(
        '0=plus(minus(x),x)', negation)
    flipped_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', associativity)
    if stop_before_free_instantiation:
        return prover.qed()
    step7 = prover.add_free_instantiation(
        '0=plus(minus(minus(x)),minus(x))', flipped_negation, {'x': 'minus(x)'})
    step8 = prover.add_flipped_equality(
        'plus(minus(minus(x)),minus(x))=0', step7)
    step9 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),minus(x)),x)='
        'plus(minus(minus(x)),plus(minus(x),x))',
        associativity, {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step10 = prover.add_free_instantiation('plus(0,0)=0', zero, {'x': '0'})
    step11 = prover.add_free_instantiation(
        'plus(x,0)=plus(0,plus(x,0))', flipped_zero, {'x': 'plus(x,0)'})
    step12 = prover.add_free_instantiation(
        'plus(0,plus(x,0))=plus(plus(0,x),0)', flipped_associativity,
        {'x': '0', 'y': 'x', 'z': '0'})
    if stop_before_substituted_equality:
        return prover.qed()
    step13 = prover.add_substituted_equality(
        'plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)',
        step7, 'plus(plus(_,x),0)')
    step14 = prover.add_substituted_equality(
        'plus(plus(plus(minus(minus(x)),minus(x)),x),0)='
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)',
        step9, 'plus(_,0)')
    step15 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)='
        'plus(plus(minus(minus(x)),0),0)',
        negation, 'plus(plus(minus(minus(x)),_),0)')
    step16 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))',
        associativity, {'x': 'minus(minus(x))', 'y': '0', 'z': '0'})
    step17 = prover.add_substituted_equality(
        'plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)',
        step10, 'plus(minus(minus(x)),_)')
    step18 = prover.add_substituted_equality(
        'plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))',
        flipped_negation, 'plus(minus(minus(x)),_)')
    step19 = prover.add_free_instantiation(
        'plus(minus(minus(x)),plus(minus(x),x))='
        'plus(plus(minus(minus(x)),minus(x)),x)', flipped_associativity,
        {'x': 'minus(minus(x))','y': 'minus(x)','z': 'x'})
    step20 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)', step8, 'plus(_,x)')
    if stop_before_chained_equality:
        return prover.qed()
    step21 = prover.add_chained_equality(
        'plus(x,0)=x',
        [step11, step12, step13, step14, step15, step16, step17, step18, step19,
         step20, zero])
    return prover.qed()

def unique_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms and from the assumption a+c=a
    (``'plus(a,c)=a'``) that c=0 (``'c=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS.union({'plus(a,c)=a'}), print_as_proof_forms)

    # Setup
    zero_addition_assumption = prover.add_assumption('plus(0,x)=x')
    associative_rule = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')

    associative_rule_flipped = prover.add_flipped_equality('plus(x,plus(y,z))=plus(plus(x,y),z)', associative_rule)
    cancel_vars = prover.add_free_instantiation('plus(minus(a),plus(a,c))=plus(plus(minus(a),a),c)',
                                                associative_rule_flipped, {'x': 'minus(a)', 'y': 'a', 'z': 'c'})
    negation_rule = prover.add_assumption('plus(minus(x),x)=0')
    negate_a = prover.add_free_instantiation('plus(minus(a),a)=0', negation_rule, {'x': 'a'})
    zero_a = prover.add_free_instantiation('plus(0,a)=a', zero_addition_assumption, {'x': 'a'})

    # The proof steps
    step1 = prover.add_assumption('plus(a,c)=a')

    step2 = prover.add_free_instantiation('plus(0,a)=a', zero_addition_assumption, {'x': 'a'})
    step3 = prover.add_flipped_equality('a=plus(0,a)', step2)
    step4 = prover.add_chained_equality('plus(a,c)=plus(0,a)', [step1, step3])

    step5 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),plus(0,a))',
                                            step4, 'plus(minus(a),_)')
    step6 = prover.add_substituted_equality('plus(plus(minus(a),a),c)=plus(0,c)', negate_a, 'plus(_,c)')
    step7 = prover.add_free_instantiation('plus(0,c)=c', zero_addition_assumption, {'x': 'c'})
    step8 = prover.add_substituted_equality('plus(minus(a),plus(0,a))=plus(minus(a),a)', zero_a, 'plus(minus(a),_)')

    step9 = prover.add_flipped_equality('c=plus(0,c)', step7)
    step10 = prover.add_flipped_equality('plus(0,c)=plus(plus(minus(a),a),c)', step6)
    step11 = prover.add_flipped_equality('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))', cancel_vars)

    prover.add_chained_equality('c=0',  [step9, step10, step11, step5, step8, negate_a])
    return prover.qed()

#: The six field axioms
FIELD_AXIOMS = frozenset(GROUP_AXIOMS.union(
    {'plus(x,y)=plus(y,x)', 'times(x,1)=x', 'times(x,y)=times(y,x)',
     'times(times(x,y),z)=times(x,times(y,z))', '(~x=0->Ey[times(y,x)=1])',
     'times(x,plus(y,z))=plus(times(x,y),times(x,z))'}))

def multiply_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the field axioms that 0*x=0 (``'times(0,x)=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(FIELD_AXIOMS, print_as_proof_forms)

    # Define some basic fields set rules
    zero_value_rule = prover.add_assumption('plus(0,x)=x')
    commutativity_rule = prover.add_assumption('times(x,y)=times(y,x)')
    associativity_rule = prover.add_assumption('times(x,plus(y,z))=plus(times(x,y),times(x,z))')

    # Begin the proof
    step1 = prover.add_free_instantiation('plus(0,0)=0', zero_value_rule, {'x': '0'})
    step2 = prover.add_substituted_equality('times(plus(0,0),x)=times(0,x)', step1, Term.parse('times(_,x)'))
    step3 = prover.add_flipped_equality('times(0,x)=times(plus(0,0),x)', step2)
    step4 = prover.add_free_instantiation('times(plus(0,0),x)=times(x,plus(0,0))',
                                          commutativity_rule, {'x': 'plus(0,0)', 'y': 'x'})
    step5 = prover.add_free_instantiation('times(x,plus(0,0))=plus(times(x,0),times(x,0))',
                                          associativity_rule, {'x': 'x', 'y': '0', 'z': '0'})
    step6 = prover.add_free_instantiation('times(x,0)=times(0,x)',
                                          commutativity_rule, {'x': 'x', 'y': '0'})
    step7 = prover.add_substituted_equality('plus(times(x,0),times(x,0))=plus(times(0,x),times(0,x))',
                                            step6, 'plus(_,_)')
    step8 = prover.add_chained_equality('times(0,x)=plus(times(0,x),times(0,x))', [step3, step4, step5, step7])

    # We shown that 0*x=(0*x)+(0*x). The rest can be done based on Task 10.10
    # SO - Setup addition rules:
    associative_rule = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    associative_rule_flipped = prover.add_flipped_equality('plus(x,plus(y,z))=plus(plus(x,y),z)', associative_rule)
    cancel_vars = prover.add_free_instantiation(
        'plus(minus(times(0,x)),plus(times(0,x),times(0,x)))=plus(plus(minus(times(0,x)),times(0,x)),times(0,x))',
        associative_rule_flipped, {
            'x': 'minus(times(0,x))',
            'y': 'times(0,x)',
            'z': 'times(0,x)'
        })
    negation_rule = prover.add_assumption('plus(minus(x),x)=0')
    negate_a = prover.add_free_instantiation('plus(minus(times(0,x)),times(0,x))=0', negation_rule, {'x': 'times(0,x)'})
    zero_a = prover.add_free_instantiation('plus(0,times(0,x))=times(0,x)', zero_value_rule, {'x': 'times(0,x)'})

    # And continue the proof
    step9 = prover.add_flipped_equality('plus(times(0,x),times(0,x))=times(0,x)', step8)

    step10 = prover.add_free_instantiation('plus(0,times(0,x))=times(0,x)', zero_value_rule, {'x': 'times(0,x)'})
    step11 = prover.add_flipped_equality('times(0,x)=plus(0,times(0,x))', step10)
    step12 = prover.add_chained_equality('plus(times(0,x),times(0,x))=plus(0,times(0,x))', [step9, step11])
    step13 = prover.add_substituted_equality(
        'plus(minus(times(0,x)),plus(times(0,x),times(0,x)))=plus(minus(times(0,x)),plus(0,times(0,x)))',
        step12,
        'plus(minus(times(0,x)),_)')

    step14 = prover.add_substituted_equality('plus(plus(minus(times(0,x)),times(0,x)),times(0,x))=plus(0,times(0,x))',
                                             negate_a,
                                             'plus(_,times(0,x))')
    step15 = prover.add_free_instantiation('plus(0,times(0,x))=times(0,x)', zero_value_rule, {'x': 'times(0,x)'})
    step16 = prover.add_substituted_equality(
        'plus(minus(times(0,x)),plus(0,times(0,x)))=plus(minus(times(0,x)),times(0,x))', zero_a,
        'plus(minus(times(0,x)),_)')

    # Conclusion
    step17 = prover.add_flipped_equality('times(0,x)=plus(0,times(0,x))', step15)
    step18 = prover.add_flipped_equality('plus(0,times(0,x))=plus(plus(minus(times(0,x)),times(0,x)),times(0,x))', step14)
    step19 = prover.add_flipped_equality(
        'plus(plus(minus(times(0,x)),times(0,x)),times(0,x))=plus(minus(times(0,x)),plus(times(0,x),times(0,x)))',
        cancel_vars)

    prover.add_chained_equality('times(0,x)=0', [step17, step18, step19, step13, step16, negate_a])
    return prover.qed()

#: The induction axiom
INDUCTION_AXIOM = Schema(
    Formula.parse('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])'), {'R'})
#: The six axioms of Peano arithmetic
PEANO_AXIOMS = frozenset({'(s(x)=s(y)->x=y)', '(~x=0->Ey[s(y)=x])', '~s(x)=0',
                          'plus(x,0)=x', 'plus(x,s(y))=s(plus(x,y))',
                          'times(x,0)=0', 'times(x,s(y))=plus(times(x,y),x)',
                          INDUCTION_AXIOM})

def peano_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms of Peano arithmetic that 0+x=x
    (``'plus(0,x)=x'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(PEANO_AXIOMS, print_as_proof_forms)

    # Setup the assumptions
    step1 = prover.add_assumption('plus(x,0)=x')

    # Begin the proof itself
    step2 = prover.add_free_instantiation('plus(0,0)=0', step1, {'x': '0'})
    step3 = prover.add_instantiated_assumption('(plus(0,x)=x->(plus(0,s(x))=s(plus(0,x))->plus(0,s(x))=s(x)))',
                                               prover.ME, {
                                                   'R': 'plus(0,s(x))=s(_)',
                                                   'c': 'plus(0,x)',
                                                   'd': 'x'
                                               })
    step4 = prover.add_assumption('plus(x,s(y))=s(plus(x,y))')
    step5 = prover.add_free_instantiation('plus(0,s(x))=s(plus(0,x))', step4, {'x': '0', 'y': 'x'})
    step6 = prover.add_tautological_implication('(plus(0,x)=x->plus(0,s(x))=s(x))', {step3, step5})
    step7 = prover.add_ug('Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]', step6)

    # Get to some conclusions
    step8 = prover.add_tautology(
        '(plus(0,0)=0->(Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]->(plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])))')
    step9 = prover.add_mp('(Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]->(plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]))',
                          step2, step8)
    step10 = prover.add_mp('(plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])', step7, step9)
    step11 = prover.add_instantiated_assumption('((plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])->Ax[plus(0,x)=x])',
                                                INDUCTION_AXIOM, {
                                                    'R': 'plus(0,_)=_'
                                                })
    step12 = prover.add_mp('Ax[plus(0,x)=x]', step10, step11)
    prover.add_universal_instantiation('plus(0,x)=x', step12, 'x')

    return prover.qed()

#: The axiom schema of (unrestricted) comprehension
COMPREHENSION_AXIOM = Schema(
    Formula.parse('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]'), {'R'})

def russell_paradox_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms schema of unrestricted comprehension the
    contradiction ``'(z=z&~z=z)'``.

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({COMPREHENSION_AXIOM}, print_as_proof_forms)

    # Add our assumptions
    step1 = prover.add_instantiated_assumption(
        'Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]',
        COMPREHENSION_AXIOM, {'R': '~In(_,_)'})
    step2 = prover.add_instantiated_assumption(
        "(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y))))", Prover.UI, {
            'R': '((In(_,y)->~In(_,_))&(~In(_,_)->In(_,y)))',
            'x': 'x',
            'c': 'y'
        })
    step3 = prover.add_instantiated_assumption(
        "(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->Ey[((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))])", Prover.EI, {
            'R': '((In(_,_)->~In(_,_))&(~In(_,_)->In(_,_)))',
            'x': 'y',
            'c': 'y'
        })

    # Conclude
    step4 = prover.add_tautological_implication(
        "(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->Ey[((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))])",
        {step2, step3})

    step5 = prover.add_existential_derivation('Ey[((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))]', step1, step4)
    step6 = prover.add_tautology('(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(z=z&~z=z))')

    prover.add_existential_derivation('(z=z&~z=z)', step5, step6)

    return prover.qed()

def not_exists_not_implies_all_proof(formula: Formula, variable: str,
                                     print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(~E``\ `variable`\ ``[~``\ `formula`\ ``]->A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.1

def exists_not_implies_not_all_proof(formula: Formula, variable: str,
                                     print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(E``\ `variable`\ ``[~``\ `formula`\ ``]->~A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.2

def not_all_iff_exists_not_proof(formula: Formula, variable: str,
                                 print_as_proof_forms: bool = False) -> Proof:
    """Proves that
    `equivalence_of`\ ``('(~A``\ `variable`\ ``[``\ `formula`\ ``]', 'E``\ `variable`\ ``[~``\ `formula`\ ``]')``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.3
