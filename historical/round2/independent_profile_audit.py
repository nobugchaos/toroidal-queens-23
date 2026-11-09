"""Independent exact audit: Gosper masks + vectorized difference-diagonal test.

Does not import the primary enumeration or its polynomial/moment-rank routines.
Integer masks fit in uint32. No floating-point arithmetic is used.
"""
import hashlib
import json
from pathlib import Path
import time
import numpy as np

ROOT = Path(__file__).resolve().parent


def enumerate_masks(p,k):
    profiles = [[] for _ in range(p)]
    mask = (1 << k)-1
    end = 1 << p
    checked = 0
    while mask < end:
        checked += 1
        total = total2 = total3 = 0
        bits = mask
        while bits:
            low = bits & -bits
            value = low.bit_length()-1
            total += value
            total2 += value*value
            total3 += value*value*value
            bits -= low
        if total % p == 0 and total3 % p == 0:
            profiles[total2 % p].append(mask)
        low = mask & -mask
        changed = mask+low
        mask = changed | (((changed ^ mask) >> 2)//low)
    return profiles,checked


def rotate(mask,d,p):
    d %= p
    return ((mask << d) | (mask >> (p-d))) & ((1 << p)-1)


def halve(mask,p):
    answer = 0
    inverse_two = pow(2,-1,p)
    for i in range(p):
        if mask >> i & 1:
            answer |= 1 << (i*inverse_two % p)
    return answer


def required_differences(row,col,summ,p):
    all_mask = (1 << p)-1
    unoccupied = all_mask ^ row
    half = halve(summ,p)
    inv = pow(2,-1,p)
    return [d for d in range(p) if unoccupied & ~rotate(col,d,p) & ~rotate(half,d*inv,p)]


def known_p11_control():
    p = 11
    # Published five-queen solution translated by its coordinate mean (4,2).
    points = [((r-4) % p,(c-2) % p) for r,c in [(0,0),(2,6),(4,2),(6,9),(8,4)]]
    row = sum(1 << r for r,c in points)
    col = sum(1 << c for r,c in points)
    summ = sum(1 << ((r+c) % p) for r,c in points)
    diff = sum(1 << ((r-c) % p) for r,c in points)
    assert all(mask.bit_count() == 5 for mask in (row,col,summ,diff))
    profiles,count = enumerate_masks(11,5)
    norm = sum(r*r for r,c in points) % p
    assert row in profiles[norm] and col in profiles[norm]
    assert summ in profiles[2*norm % p] and diff in profiles[2*norm % p]
    needed = required_differences(row,col,summ,p)
    assert len(needed) <= 5
    assert all(diff >> d & 1 for d in needed)
    for r in range(p):
        for c in range(p):
            assert any(r == a or c == b or (r+c-a-b) % p == 0 or (r-c-a+b) % p == 0 for a,b in points)
    return {'status':'PASS','p':p,'queens':5,'required_difference_count':len(needed),'centered_positions':points}


def run():
    start = time.time()
    profiles,checked = enumerate_masks(23,11)
    published = json.loads((ROOT/'profiles.json').read_text())['profiles']
    assert all(len(a) == len(set(a)) and sorted(a) == sorted(b) for a,b in zip(profiles,published))
    stats = []
    inv = pow(2,-1,23)
    all_mask = (1 << 23)-1
    min_seen = 23
    closest = None
    for norm in range(23):
        group = profiles[norm]
        diagonals = profiles[2*norm % 23]
        rows_empty = np.array([all_mask ^ row for row in group],dtype=np.uint32)
        local_min = 23
        triples = 0
        for col in group:
            col_shift = np.array([rotate(col,d,23) for d in range(23)],dtype=np.uint32)
            for summ in diagonals:
                half = halve(summ,23)
                sum_shift = np.array([rotate(half,d*inv,23) for d in range(23)],dtype=np.uint32)
                allowed_rows = np.bitwise_not(np.bitwise_or(col_shift,sum_shift)) & all_mask
                required = np.count_nonzero(np.bitwise_and(rows_empty[:,None],allowed_rows[None,:]),axis=1)
                assert required.size == len(group)
                assert np.all(required >= 12), {'norm':norm,'col':col,'sum':summ}
                current = int(required.min())
                if current < min_seen:
                    index = int(required.argmin())
                    row = group[index]
                    actual = required_differences(row,col,summ,23)
                    assert len(actual) == current
                    min_seen = current
                    closest = {'norm':norm,'row':row,'col':col,'sum':summ,'required_differences':actual}
                local_min = min(local_min,current)
                triples += len(group)
        stats.append({'norm':norm,'triples':triples,'minimum_required_difference_lines':local_min})
        print(json.dumps(stats[-1]),flush=True)
    result = {'status':'PASS','claim':'All centered profiles require at least twelve difference lines.',
              'combinations_checked':checked,'profile_counts':[len(g) for g in profiles],
              'total_triples':sum(s['triples'] for s in stats),'stats':stats,
              'global_minimum_required_difference_lines':min_seen,'closest_profile':closest,
              'positive_control_p11':known_p11_control(),'seconds':time.time()-start,
              'numpy':np.__version__,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'profiles_sha256':hashlib.sha256((ROOT/'profiles.json').read_bytes()).hexdigest(),
              'scope':'Finite enumeration only. Analytic moment implication is proved separately.'}
    (ROOT/'independent-profile-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({key:value for key,value in result.items() if key != 'stats'}),flush=True)


if __name__ == '__main__':
    run()
