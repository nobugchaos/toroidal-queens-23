"""Small independent LRAT verifier for the RUP-only subset.

No solver code is imported. Negative RAT hints are rejected. Each added clause
must follow by unit propagation under its negation; a checked empty clause is
required. This is executable verification, not a Lean-kernel certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parent


def rup(clause,hints,formula):
    assignment = {}
    for literal in clause:
        variable = abs(literal)
        value = literal < 0
        if variable in assignment and assignment[variable] != value:
            return True  # A tautological added clause needs no propagation.
        assignment[variable] = value
    for hint in hints:
        if hint <= 0:
            raise ValueError('RAT or invalid hints are outside this checker.')
        if hint not in formula:
            raise ValueError(f'Missing/deleted antecedent {hint}')
        unit = 0
        count = 0
        satisfied = False
        for literal in formula[hint]:
            value = assignment.get(abs(literal))
            if value is None:
                unit = literal
                count += 1
            elif value == (literal > 0):
                satisfied = True
                break
        if satisfied:
            continue
        if count == 0:
            return True
        if count != 1:
            raise ValueError(f'Antecedent {hint} is neither unit nor false')
        assignment[abs(unit)] = unit > 0
    return False


def parse_cnf(path):
    formula = {}
    header = None
    tokens = []
    for line in Path(path).read_text(encoding='ascii').splitlines():
        if not line or line.startswith('c'):
            continue
        if line.startswith('p '):
            _,kind,n,m = line.split()
            assert kind == 'cnf'
            header = (int(n),int(m))
            continue
        tokens.extend(map(int,line.split()))
    assert header is not None
    clause = []
    for literal in tokens:
        if literal:
            assert 1 <= abs(literal) <= header[0]
            clause.append(literal)
        else:
            formula[len(formula)+1] = tuple(clause)
            clause = []
    assert not clause and len(formula) == header[1]
    return formula,header


def verify(cnf,proof):
    start = time.time()
    formula,header = parse_cnf(cnf)
    initial_clauses = len(formula)
    additions = deletions = hint_count = 0
    empty_id = None
    previous = initial_clauses
    with Path(proof).open(encoding='ascii') as inp:
        for line_number,line in enumerate(inp,1):
            parts = line.split()
            if not parts or parts[0] == 'c':
                continue
            identifier = int(parts[0])
            if parts[1] == 'd':
                assert parts[-1] == '0'
                for s in parts[2:-1]:
                    key = int(s)
                    formula.pop(key,None)
                    deletions += 1
                continue
            assert identifier > previous and identifier not in formula
            previous = identifier
            values = list(map(int,parts[1:]))
            pivot = values.index(0)
            clause = tuple(values[:pivot])
            assert values[-1] == 0 and 0 not in values[pivot+1:-1]
            hints = values[pivot+1:-1]
            if not rup(clause,hints,formula):
                raise ValueError(f'Clause {identifier}, line {line_number}: no propagation contradiction')
            formula[identifier] = clause
            additions += 1
            hint_count += len(hints)
            if not clause:
                empty_id = identifier
                break
    if empty_id is None:
        raise ValueError('No checked empty clause; not an UNSAT certificate.')
    result = {'status':'PASS_RUP_REFUTATION','cnf':Path(cnf).name,'proof':Path(proof).name,
              'variables':header[0],'initial_clauses':initial_clauses,'checked_additions':additions,
              'deleted_clause_references':deletions,'positive_hints_checked':hint_count,
              'empty_clause_id':empty_id,'seconds':time.time()-start,
              'cnf_sha256':hashlib.sha256(Path(cnf).read_bytes()).hexdigest(),
              'proof_sha256':hashlib.sha256(Path(proof).read_bytes()).hexdigest(),
              'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'scope':'Propositional refutation only; profile completeness and moment bridge are separate.'}
    out = Path(proof).with_name(Path(proof).stem+'-checked.json')
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result),flush=True)
    return result


def self_test():
    f = {1:(1,),2:(-1,)}
    assert rup((),[1,2],f)
    assert not rup((),[1],f)
    assert not rup((),[],f)
    assert not rup((2,),[1],{1:(1,2),2:(-1,2)})
    assert rup((2,),[1,2],{1:(1,2),2:(-1,2)})
    try:
        rup((),[-1],f)
    except ValueError:
        pass
    else:
        raise AssertionError('Negative hint was accepted')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--norm',type=int,required=True)
    args = parser.parse_args()
    self_test()
    verify(ROOT/f'profile-norm-{args.norm}.cnf',ROOT/f'profile-norm-{args.norm}.lrat')
