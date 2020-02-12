

def test_inference_proof(prover, rule, rules, debug):
    if debug:
        print('=' * 35)
        print('Testing', prover.__qualname__)
        print('')

        proof = prover()
        if proof.statement != rule:
            print('Error: proof.statement != rule')
            print('proof.statement: ', proof.statement)
            print('rule: ', rule)
            print('=' * 35)
            return False

        if not proof.is_valid() or offending_line(proof):
            print("INVALID Proof:")
            print(proof)

            if proof.lines[-1].formula != proof.statement.conclusion:
                print("The final line of the proof must be the conclusion.")
                print("Expected:", proof.statement.conclusion)
                print("Actual:", proof.lines[-1].formula)

            invalid_lines = []
            for line_number in range(0, len(proof.lines)):
                if not proof.is_line_valid(line_number):
                    invalid_lines.append(str(line_number))
            if len(invalid_lines) > 0:
                print('Invalid line(s):', ', '.join(invalid_lines))
            print('=' * 35)
            return False

        print("VALID Proof:")
        print(proof)
        print('=' * 35)
    else:
        proof = prover()
        assert proof.statement == rule
        assert proof.rules.issubset(rules), \
               "got " + str(proof.rules) + ", expected " + str(rules)
        assert proof.is_valid(), offending_line(proof)

    return True


def offending_line(proof):
    """Finds the first invalid line in the given proof.

    Parameters:
        proof: proof to search.

    Returns:
        An error message containing the line number and string representation of
        the first invalid line in the given proof, or ``None`` if all the lines
        of the given proof are valid."""
    for i in range(len(proof.lines)):
        if not proof.is_line_valid(i):
            return "Invalid Line " + str(i) + ": " + str(proof.lines[i])
    return None
