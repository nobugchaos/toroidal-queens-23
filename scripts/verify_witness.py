"""Independent integer-modulo-23 check of the twelve-queen construction."""
from pathlib import Path
import itertools,json

ROOT=Path(__file__).resolve().parents[1]

def main():
    data=json.loads((ROOT/'data/witness.json').read_text())
    n=data['board_size']
    points=[tuple(q) for q in data['queens']]
    assert n==23 and len(points)==12 and len(set(points))==12
    assert all(0<=r<n and 0<=c<n for r,c in points)
    def line(q,z):
        return q[0]==z[0] or q[1]==z[1] or (q[0]+q[1]-z[0]-z[1])%n==0 or (q[0]-q[1]-z[0]+z[1])%n==0
    assert all(not line(q,z) for q,z in itertools.combinations(points,2))
    cells=list(itertools.product(range(n),repeat=2))
    assert all(any(line(q,z) for q in points) for z in cells)
    assert all(z in points or any(q!=z and line(q,z) for q in points) for z in cells)
    print(json.dumps(dict(status='PASS_WITNESS_CHECK',board_size=n,queens=len(points),
                          attacking_pairs=0,covered_cells=len(cells),
                          scope='Finite upper-bound witness only; the lower bound is proved in Lean.')))

if __name__=='__main__':main()
