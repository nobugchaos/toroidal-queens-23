"""Independent Boolean encoding of profile coverage, with LRAT output."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent
CADICAL = Path.home()/'.elan/toolchains/leanprover--lean4---v4.34.0/bin/cadical.exe'


def build(norm):
    profiles = json.loads((ROOT/'profiles.json').read_text())['profiles']
    variables = 0
    clauses = []
    def new():
        nonlocal variables
        variables += 1
        return variables
    active = [[new() for _ in range(23)] for _ in range(4)]
    for axis,table in enumerate([profiles[norm],profiles[norm],profiles[2*norm % 23]]):
        selectors = [new() for _ in table]
        clauses.append(selectors)
        for selector,mask in zip(selectors,table):
            for j in range(23):
                clauses.append([-selector,active[axis][j] if mask >> j & 1 else -active[axis][j]])
    for r in range(23):
        for c in range(23):
            clauses.append([active[0][r],active[1][c],active[2][(r+c) % 23],active[3][(r-c) % 23]])
    # At most eleven difference-diagonals, using forced prefix thresholds.
    prev = {}
    for i,x in enumerate(active[3]):
        now = {j:new() for j in range(1,min(i+1,12)+1)}
        clauses.append([-x,now[1]])
        for j,v in prev.items():
            clauses.append([-v,now[j]])
            if j+1 in now:
                clauses.append([-x,-v,now[j+1]])
        prev = now
    clauses.append([-prev[12]])
    return variables,clauses


def run(norm,seconds):
    variables,clauses = build(norm)
    tag = f'profile-norm-{norm}'
    cnf = ROOT/f'{tag}.cnf'
    proof = ROOT/f'{tag}.lrat'
    log = ROOT/f'{tag}.log'
    with cnf.open('w',encoding='ascii',newline='\n') as out:
        out.write(f'p cnf {variables} {len(clauses)}\n')
        for clause in clauses:
            out.write(' '.join(map(str,clause))+' 0\n')
    command = [str(CADICAL),'--lrat','--no-binary',str(cnf),str(proof)]
    start = time.time()
    with log.open('w',encoding='utf-8') as out:
        process = subprocess.Popen(command,stdout=out,stderr=subprocess.STDOUT)
        try:
            code = process.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
            code = None
    result = {'norm':norm,'status':{10:'SAT',20:'UNSAT_UNCHECKED',None:'UNKNOWN_TIMEOUT'}.get(code,'ERROR'),
              'exit_code':code,'seconds':time.time()-start,'time_limit':seconds,
              'variables':variables,'clauses':len(clauses),'proof_bytes':proof.stat().st_size if proof.exists() else 0,
              'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),
              'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'command':command,'certificate_checked':False}
    (ROOT/f'{tag}-result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result),flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--norm',type=int,required=True)
    parser.add_argument('--seconds',type=float,default=120)
    args = parser.parse_args()
    run(args.norm,args.seconds)
