# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/proofs.py

"""Proofs by deduction in propositional logic."""

from __future__ import annotations
from typing import AbstractSet, Iterable, FrozenSet, List, Mapping, Optional, \
                   Set, Tuple, Union

from logic_utils import frozen

from propositions.syntax import *

SpecializationMap = Mapping[str, Formula]

import sys

INTERNAL_DEBUG = False
def proof_debug(s):
    if INTERNAL_DEBUG:
        print('[PROOF DEBUG]', s)

@frozen
class InferenceRule:
    """An immutable inference rule in propositional logic, comprised by zero
    or more assumed propositional formulae, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Iterable[Formula], conclusion: Formula) -> \
        None:
        """Initialized an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return (isinstance(other, InferenceRule) and
                self.assumptions == other.assumptions and
                self.conclusion == other.conclusion)

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current inference
        rule.

        Returns:
            A set of all atomic propositions used in the assumptions and in the
            conclusion of the current inference rule.
        """
        return self.conclusion.variables() | set([v for a in self.assumptions for v in a.variables()])

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """
        for variable in specialization_map:
            assert is_variable(variable)

        new_assumptions = []
        # Convert the assumptions
        for assumption in self.assumptions:
            new_assumptions.append(assumption.substitute_variables(specialization_map))

        # Convert the conclusion
        new_conclusion = self.conclusion.substitute_variables(specialization_map)
        return InferenceRule(new_assumptions, new_conclusion)

    @staticmethod
    def merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps.

        Parameters:
            specialization_map1: first map to merge, or ``None``.
            specialization_map2: second map to merge, or ``None``.

        Returns:
            A single map containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)

        if specialization_map1 is not None and specialization_map2 is not None:
            # Convert keys to set
            first_map_vars = set(specialization_map1.keys())
            second_map_vars = set(specialization_map2.keys())

            # Do we have any intersection?
            intersection = first_map_vars & second_map_vars
            if len(intersection) > 0:
                # The values in the intersections must be identical
                intersection_with_diff_values = any([1 for k in intersection if specialization_map1[k] != specialization_map2[k]])
                if intersection_with_diff_values:
                    return None
        else:
            # If one of the maps is None, then the merge will be None too
            return None

        # Unpack and send (https://stackoverflow.com/a/26853961)
        return {**specialization_map1, **specialization_map2}

    @staticmethod
    def formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        general_type = general.getType()

        # "If the general formula is a variable then the specialized formula may be any formula."
        if general_type == Formula.NodeType.T_VAR:
            return { general.root: specialization }

        # "Otherwise, the root of the specialized formula must be identical to the root of the general formula"
        if general.root != specialization.root:
            return None

        # Handle const with same root
        if general_type == Formula.NodeType.T_CONST:
            return {}

        # "The subtrees should match recursively according to the same conditions"
        first_specialization_map = InferenceRule.formula_specialization_map(general.first, specialization.first)
        if general_type == Formula.NodeType.T_UNARY_OP: # Both will be the same NodeType, as their root is identical.
            return first_specialization_map

        second_specialization_map = InferenceRule.formula_specialization_map(general.second, specialization.second)

        # Merge them. Note that "there is an important additional consistency
        # condition: all occurrences of each variable in the general rule must
        # correspond to the same subformula throughout the specialization".
        # Calling merge_specialization_maps will respect that.
        return InferenceRule.merge_specialization_maps(first_specialization_map, second_specialization_map)

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        # "First, the number of assumptions should match."
        if len(self.assumptions) != len(specialization.assumptions):
            proof_debug('specialization_map failed: The number of assumptions is different!' \
                    '\n- General: {} ({} assumptions)\n- Specialization: {} ({} assumptions)' \
                    .format(self, len(self.assumptions), specialization, len(specialization.assumptions)))
            return None

        # Create the specialization assumptions
        specialization_assumptions = dict()
        for i in range(0, len(self.assumptions)):
            assumption_specialization_map = InferenceRule.formula_specialization_map(
                self.assumptions[i], specialization.assumptions[i]
            )
            specialization_assumptions = InferenceRule.merge_specialization_maps(specialization_assumptions, assumption_specialization_map)

        proof_debug('Has {} assumptions:\n- General: {}\n- Specialization: {}' \
            '\n\n********************\nCreated Map: {}\n********************\n'.format(len(self.assumptions),
            self.assumptions, specialization.assumptions, specialization_assumptions))

        # Calculate the specialization conclusion
        specialization_conclusion = InferenceRule.formula_specialization_map(
                self.conclusion, specialization.conclusion
           )

        # Merge them
        return InferenceRule.merge_specialization_maps(
            specialization_assumptions, specialization_conclusion)

    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None

class ProofBuilder:
    """A utility class that's being used to build a Proof.
    This pattern is more common in Java, but as we work with immutable objects
    it'll be a lot easier this way to build the proofs."""

    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]

    def __init__(self, statement: InferenceRule=None) -> None:
        """Initializes a Proof builder.

        Parameters:
            statement: the statement for the proof."""
        self.statement = statement
        self.rules = set()
        self.lines = list()

    def with_conclusion(self, statement: InferenceRule) -> ProofBuilder:
        """Replaces the initial conclusion with the given conclusion.

        Parameters:
            statement The conclusion.

        Returns:
            The builder instance."""
        self.statement = statement
        return self

    @staticmethod
    def claim(assumption: Union[str, Formula], conclusion: Union[str, Formula]) -> ProofBuilder:
        """Builds a new claim from the given assumption, which aims to proof the given conclusion.

        Parameters:
            assumptions: An assumption, which can be a str to be parsed into a formula, or the formula tree.
            conclusion: The proof conclusion.

        Returns:
            A proof builder instance."""
        if type(assumption) is str:
            assumption = Formula.parse(assumption)
        if type(conclusion) is str:
            conclusion = Formula.parse(conclusion)

        return ProofBuilder(InferenceRule([assumption], conclusion))

    def with_rule(self, rule: InferenceRule) -> ProofBuilder:
        """Adds a rule to the proof.

        Parameters:
            rule: the rule to add to the proof.

        Returns:
            The builder instance."""
        self.rules.add(rule)
        return self

    def with_rules(self, rules: FrozenSet[InferenceRule]) -> ProofBuilder:
        """Adds a rule to the proof.

        Parameters:
            rules: A list of rules to add to the proof.

        Returns:
            The builder instance."""
        self.rules |= rules
        return self

    def add_line(self, line: Proof.Line) -> ProofBuilder:
        """Adds a line to the proof.

        Parameters:
            line: the line to add to the proof.

        Returns:
            The builder instance."""
        self.lines.append(line)
        return self

    def add_lines(self, lines: Tuple[Proof.Line], index_shifting: int=-1) -> ProofBuilder:
        """Adds lines to the proof.

        Parameters:
            lines: the lines to add to the proof.
            index_shifting: A value to shift the assumptions indexes with, or -1 if shouldn't be used.

        Returns:
            The builder instance."""
        if index_shifting == -1:
            self.lines += lines
        else:
            for line in lines:
                if line.is_assumption():
                    self.lines.append(line)
                else:
                    self.add_claim_line(line.formula, line.rule,
                                        map(lambda l: l + index_shifting, line.assumptions))

        return self

    def add_assumption_line(self, assumption: Union[Formula, str]) -> ProofBuilder:
        """Adds an assumption line.

        Parameters:
            formula: the formula to be justified by this line.

        Returns:
            The builder instance."""
        if type(assumption) is str:
            assumption = Formula.parse(assumption)

        self.lines.append(Proof.Line(assumption))
        return self

    def add_claim_line(self, formula: Union[Formula, str],
                     rule: InferenceRule,
                     assumptions: Optional[Iterable[int]] = None)-> ProofBuilder:
        """Adds a new claim line.
        Parameters:
            formula: the formula to be justified by this line.
            rule: the inference rule out of those allowed in the proof, a
                specialization of which concludes the formula.
            assumptions: an iterable over indices of previous lines in the
                proof whose formulae are the respective assumptions of the
                specialization of the rule that concludes the formula.

        Returns:
            The proof builder.
        """

        if type(formula) is str:
            formula = Formula.parse(formula)

        if assumptions is None:
            assumptions = []

        self.lines.append(Proof.Line(formula, rule, assumptions))
        return self

    def build(self) -> Proof:
        """Build the proof from the collected parameters.

            Returns:
                The builded proof"""
        assert self.statement is not None
        assert len(self.lines) > 0
        return Proof(self.statement, tuple(self.rules), tuple(self.lines))

    def index_of_assumption(self, assumption: Proof.Line):
        """Determines if the builder already contains the given assumption, and if so, in which line number.

        Parameters:
            assumption: The assumption to search.

        Returns:
            The assumption line number, of -1 if it does not exists."""
        assert assumption.is_assumption()

        for i in range(len(self.lines)):
            if not self.lines[i].is_assumption():
                continue

            if self.lines[i].formula == assumption.formula:
                return i

        return -1

    def get_last_line(self) -> Proof.Line:
        """
        Gets the builder last line.

        Returns:
            The last line instance.
        """
        return self.lines[-1]

    def get_current_line(self) -> int:
        """Gets the current Builder line.

        Returns:
            The current line (1th index, just like len(...))."""
        return len(self.lines)

    def __repr__(self) -> str:
        """Computes a string representation of the current proof line.

        Returns:
            A string representation of the current proof line.
        """

        builder = 'Proof Builder:\n'
        builder += '    - Statement to prove:       {}\n'.format(self.statement)
        builder += '    - Valid inference rules:    '
        if len(self.rules) > 0:
            rules = list(self.rules)
            builder += '\n'
            for i in range(0, len(rules)):
                builder += '        {}) {}\n'.format(i + 1, rules[i])
        else:
            builder += 'No Rules Defined\n'

        builder += '    - Proof Lines:    '
        if len(self.lines) > 0:
            builder += '\n'
            for i in range(0, len(self.lines)):
                builder += '        {}) {}\n'.format(i + 1, self.lines[i])
        else:
            builder += 'No Lines Defined\n'

        return builder.strip()

@frozen
class Proof:
    """A frozen deductive proof, comprised of a statement in the form of an
    inference rule, a set of inference rules that may be used in the proof, and
    a proof in the form of a list of lines that prove the statement via these
    inference rules.

    Attributes:
        statement (`InferenceRule`): the statement of the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]

    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Iterable[Proof.Line]) -> None:
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement for the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula which
        is either justified as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule out
                of those allowed in the proof, a specialization of which
                concludes the formula, or ``None`` if the formula is justified
                as an assumption of the proof.
            assumptions
                (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): a tuple of zero
                or more indices of previous lines in the proof whose formulae
                are the respective assumptions of the specialization of the rule
                that concludes the formula, if the formula is not justified as
                an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Iterable[int]] = None) -> None:
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and indices of justifying previous lines.

            Parameters:
                formula: the formula to be justified by this line.
                rule: the inference rule out of those allowed in the proof, a
                    specialization of which concludes the formula, or ``None``
                    if the formula is to be justified as an assumption of the
                    proof.
                assumptions: an iterable over indices of previous lines in the
                    proof whose formulae are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current proof line.

            Returns:
                A string representation of the current proof line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                return str(self.formula) + ' Inference Rule ' + \
                       str(self.rule) + \
                       ((" on " + str(self.assumptions))
                        if len(self.assumptions) > 0 else '')

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None

    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof for ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += "Lines:\n"
        for i in range(len(self.lines)):
            r += ("%3d) " % i) + str(self.lines[i]) + '\n'
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulae justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: index of the line according to which to construct the
                inference rule.

        Returns:
            The constructed inference rule, with assumptions ordered in the
            order of their indices in the specified line, or ``None`` if the
            specified line is justified as an assumption.
        """
        assert line_number < len(self.lines)

        # Line zero doesn't have any rules
        if line_number == 0:
            return None

        # Get the assumptions
        assumptions = []
        for assumption in self.lines[line_number].assumptions:
            assumptions.append(self.lines[assumption].formula)

        # Build
        return InferenceRule(assumptions, self.lines[line_number].formula)

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: index of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            then ``True`` if and only if all of the following hold:

            1. The rule specified for that line is one of the allowed inference
               rules in the current proof.
            2. Some specialization of the rule specified for that line has
               the formula justified by that line as its conclusion, and the
               formulae justified by the lines specified as the assumptions of
               that line (in the order of their indices in this line) as its
               assumptions.
        """
        assert line_number < len(self.lines)
        line = self.lines[line_number]

        # Is this an assumption line?
        if line.is_assumption():
            for assumption in self.statement.assumptions:
                if assumption == line.formula:
                    return True
            return False

        # Is this line based on previous only assumptions?
        if len(line.assumptions) > 0 and max(line.assumptions) >= line_number:
            proof_debug("Line {} invalid: It is based on assumptions further than it (max based: {}).".format(line_number, max(line.assumptions)))
            return False

        # Check if the rule is one of the allowed inference rules?
        if not line.rule in self.rules:
            proof_debug("Line {} invalid: It uses an un-allowed rule: {}".format(line_number, line.rule))
            return False

        # Check if the line rule is a specialization of the inference rule
        result = self.rule_for_line(line_number)
        if result is None:
            proof_debug("Could not create a specialization rule for line {}. It's valid.".format(line_number))
            return True

        proof_debug('Checking if {} is a specialization of {}'.format(result, line.rule))
        return result.is_specialization_of(line.rule)


    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # First check that we reach the final conclusion, if the proof is real
        if self.lines[-1].formula != self.statement.conclusion:
            return False

        # Check general validity
        for line_number in range(0, len(self.lines)):
            if not self.is_line_valid(line_number):
                return False

        return True

# Chapter 5 tasks


def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule into a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the conclusion of the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)

    # Build a specialization map for this proof
    specialization_map = proof.statement.specialization_map(specialization)

    # Setup
    builder = ProofBuilder(specialization) \
        .with_rules(proof.rules)

    for line in proof.lines:
        specialized_line_formula = line.formula.substitute_variables(specialization_map)
        if line.is_assumption():
            # Just add the specialized assumption
            builder.add_assumption_line(specialized_line_formula)
        else:
            # Resolve the specialized rule
            builder.add_claim_line(specialized_line_formula, line.rule, line.assumptions)

    return builder.build()


def inline_proof_once(main_proof: Proof, line_number: int, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line_number: index of the line in `main_proof` that should be replaced.
        lemma_proof:: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating line indices specified throughout the proof to maintain the
        validity of the proof. The set of allowed inference rules in the
        returned proof is the union of the rules allowed in the two given
        proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()

    # Create a specialized lemma proof
    specialized_lemma_proof = prove_specialization(lemma_proof, main_proof.rule_for_line(line_number))

    # Prepare the builder
    detailed_proof = ProofBuilder(main_proof.statement) \
        .with_rules(main_proof.rules.union(specialized_lemma_proof.rules))

    # Append every line before the replaced line
    detailed_proof.add_lines(main_proof.lines[:line_number])

    # Modify the specialized lemma to fit the original proof
    modified_line = main_proof.lines[line_number]

    for lemma_line in specialized_lemma_proof.lines:
        if lemma_line.is_assumption() and lemma_line.formula not in main_proof.statement.assumptions:
            # Computes the assumption line
            assumptions = filter(lambda l: main_proof.lines[l].formula == lemma_line.formula, modified_line.assumptions)
            assumption_line = list(assumptions)[0]

            # Adds the lemma line as a claim with the main proof data
            detailed_proof.add_claim_line(lemma_line.formula, main_proof.lines[assumption_line].rule,
                                          main_proof.lines[assumption_line].assumptions)
        elif lemma_line.is_assumption() and lemma_line.formula in main_proof.statement.assumptions:
            # Append the lemma assumption
            detailed_proof.add_line(lemma_line)
        else:
            # Shift up the assumption and add the claim
            assumptions = tuple(map(lambda l: l + line_number, lemma_line.assumptions))
            detailed_proof.add_claim_line(lemma_line.formula, lemma_line.rule, assumptions)

    # Add the rest of the lines
    for proof_line in main_proof.lines[line_number + 1:]:
        if proof_line.is_assumption():
            detailed_proof.add_line(proof_line)
        else:
            # Shift up the assumption lines
            assumptions = map(lambda l: l + len(specialized_lemma_proof.lines) - 1
                if l >= line_number else l, proof_line.assumptions)

            # Append
            detailed_proof.add_claim_line(proof_line.formula, proof_line.rule, tuple(assumptions))

    return detailed_proof.build()


def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specialization
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the rules
        allowed in the two given proofs but without the "lemma" rule proved by
        `lemma_proof`.
    """
    # That's a Supercalifragilisticexpialidocious proof. Ha.
    super_detailed_proof = main_proof

    line_number = 0
    for line in super_detailed_proof.lines:
        if line.rule == lemma_proof.statement:
            # Replace with inline proof
            super_detailed_proof = inline_proof_once(super_detailed_proof, line_number, lemma_proof)
            line_number += len(lemma_proof.lines)
        else:
            line_number += 1

    # Create a new proof, w/o the lemma as an assumption
    # Note: no need to use the verbose Builder here.
    return Proof(super_detailed_proof.statement,
                 super_detailed_proof.rules.difference({ lemma_proof.statement }), super_detailed_proof.lines)
