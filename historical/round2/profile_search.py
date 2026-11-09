"""Exact line-profile enumeration using necessary centered moment constraints.

This file supplies finite computations; the analytic implication to moments must
be proved separately. Profile coverage need not imply eleven independent queens.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parent
P = 23
K = 11
ALL = (1 << P)-1


def make_profiles():
    squares = [i*i % P for i in range(P)]
    cubes = [i*i*i % P for i in range(P)]
    profiles = [[] for _ in range(P)]
    count = 0
    for row in itertools.combinations(range(P),K):
        count += 1
        if sum(row) % P or sum(cubes[i] for i in row) % P:
            continue
        norm = sum(squares[i] for i in row) % P
        mask = sum(1 << i for i in row)
        profiles[norm].append(mask)
    result = {'p':P,'k':K,'combinations_checked':count,'counts':[len(a) for a in profiles],
              'profiles':profiles,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'profiles.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    return profiles


def values(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def search(profiles,norms):
    started = time.time()
    total_stats = []
    hits = []
    for a in norms:
        row_profiles = profiles[a]
        diagonal_profiles = profiles[2*a % P]
        d_lookup = set(diagonal_profiles)
        stats = Counter()
        for row in row_profiles:
            unoccupied_rows = list(values(ALL ^ row))
            for col in row_profiles:
                stats['row_col_pairs'] += 1
                unoccupied_cols = list(values(ALL ^ col))
                # For each unoccupied sum-diagonal, collect necessary difference lines.
                by_sum = [0]*P
                for r in unoccupied_rows:
                    for c in unoccupied_cols:
                        by_sum[(r+c) % P] |= 1 << ((r-c) % P)
                for summ in diagonal_profiles:
                    stats['triples_checked'] += 1
                    needed = 0
                    for s in values(ALL ^ summ):
                        needed |= by_sum[s]
                        if needed.bit_count() > K:
                            break
                    else:
                        stats['small_required_difference'] += 1
                        possibilities = [needed] if needed.bit_count() == K else diagonal_profiles
                        for diff in possibilities:
                            if diff in d_lookup and needed & ~diff == 0:
                                hit = {'norm':a,'row':row,'col':col,'sum':summ,'diff':diff}
                                hits.append(hit)
                                stats['covering_quadruples'] += 1
                                print('COVER',json.dumps(hit),flush=True)
        total_stats.append({'norm':a,**stats,'seconds_cumulative':time.time()-started})
        print(json.dumps(total_stats[-1]),flush=True)
    result = {'status':'FINITE_LINE_PROFILE_ENUMERATION','norms':norms,'stats':total_stats,'covers':hits,
              'seconds':time.time()-started,'profiles_sha256':hashlib.sha256((ROOT/'profiles.json').read_bytes()).hexdigest(),
              'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'profile-cover-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    return result


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--norms',nargs='+',type=int,default=[0,1,22])
    ap.add_argument('--generate-only',action='store_true')
    args = ap.parse_args()
    start = time.time()
    profiles = make_profiles()
    print(json.dumps({'profile_counts':[len(a) for a in profiles],'seconds':time.time()-start}),flush=True)
    if not args.generate_only:
        search(profiles,args.norms)
