"""Generate explicit four-factor bookkeeping; Lean validates identities/degrees."""
from pathlib import Path
from itertools import combinations
root=Path(__file__).resolve().parent.parent
names=['px','py','ps','pd']
letters='RCSD'
out=['import ToroidalQueens23.Kernels','import Mathlib.Tactic.LinearCombination',
     '', 'set_option maxHeartbeats 4000000','set_option maxRecDepth 100000',
     '', 'namespace ToroidalQueens23','noncomputable section','', '''
theorem degree_add_bound {a b : Poly} {n : Nat}
    (ha : a.totalDegree ≤ n) (hb : b.totalDegree ≤ n) :
    (a+b).totalDegree ≤ n := (MvPolynomial.totalDegree_add _ _).trans (max_le ha hb)

theorem degree_pow_bound {z : Poly} (hz : z.totalDegree ≤ 1) (n : Nat) :
    (z^n).totalDegree ≤ n := by
  simpa using (MvPolynomial.totalDegree_pow z n).trans (Nat.mul_le_mul_left n hz)

theorem degree_C_pow_bound {z : Poly} (hz : z.totalDegree ≤ 1) (c : F) (n : Nat) :
    (MvPolynomial.C c*z^n).totalDegree ≤ n := by
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using degree_pow_bound hz n)

def jetB (z : Poly) (u v : F) (e : Poly) : Poly :=
  MvPolynomial.C u*z^9+MvPolynomial.C v*z^8+e

def jet (z : Poly) (u v : F) (e : Poly) : Poly := z^11+jetB z u v e

theorem jetB_degree {z e : Poly} (hz : z.totalDegree ≤ 1) (he : e.totalDegree ≤ 7)
    (u v : F) : (jetB z u v e).totalDegree ≤ 9 := by
  exact degree_add_bound (degree_add_bound (degree_C_pow_bound hz u 9)
    ((degree_C_pow_bound hz v 8).trans (by decide))) (he.trans (by decide))
''']
args='(uR uC uS uD vR vC vS vD : F) (eR eC eS eD : Poly)'
terms=[]
# single error terms
for t in range(4):
    fac=[f'{z}^11' for z in names]
    fac[t]='e'+letters[t]
    bounds=[f'(degree_pow_bound {z}_degree 11)' for z in names]
    bounds[t]='he'+letters[t]
    terms.append(('*'.join(fac),bounds))
for k in (2,3,4):
    for inds in combinations(range(4),k):
        fac=[f'{z}^11' for z in names]
        bounds=[f'(degree_pow_bound {z}_degree 11)' for z in names]
        for t in inds:
            z=names[t]; l=letters[t]
            fac[t]=f'(jetB {z} u{l} v{l} e{l})'
            bounds[t]=f'(jetB_degree {z}_degree he{l} u{l} v{l})'
        terms.append(('*'.join(fac),bounds))
out.append(f'def jetError {args} : Poly :=\n  '+'+\n  '.join(e for e,_ in terms)+'\n')
out.append(f'theorem jetError_degree {args}\n    (heR : eR.totalDegree ≤ 7) (heC : eC.totalDegree ≤ 7)\n    (heS : eS.totalDegree ≤ 7) (heD : eD.totalDegree ≤ 7) :\n    (jetError uR uC uS uD vR vC vS vD eR eC eS eD).totalDegree ≤ 40 := by\n  unfold jetError')
for i,(_,bounds) in enumerate(terms):
    if i < len(terms)-1:
        # add tree is left associative: deal with last summand, recurse to left.
        pass
def degree_tree(ts,indent='  '):
    if len(ts)==1:
        return [indent+'exact (degree_four '+' '.join(ts[0][1])+').trans (by decide)']
    return [indent+'apply degree_add_bound']+degree_tree(ts[:-1],indent+'· ')+degree_tree(ts[-1:],indent+'· ')
# Use Lean bullet blocks with two more spaces, not nested bullet prefixes.
def degree_tree(ts,indent='  '):
    if len(ts)==1:
        return [indent+'exact (degree_four '+' '.join(ts[0][1])+').trans (by decide)']
    a=degree_tree(ts[:-1],indent+'  ')
    b=degree_tree(ts[-1:],indent+'  ')
    a[0]=indent+'· '+a[0].lstrip()
    b[0]=indent+'· '+b[0].lstrip()
    return [indent+'apply degree_add_bound']+a+b
out.extend(degree_tree(terms))
out.append('')
product='*'.join(f'(jet {z} u{l} v{l} e{l})' for z,l in zip(names,letters))
components=['topKernel']
for j in (2,3):
    for l in letters:
        components.append(f'MvPolynomial.C {"u" if j==2 else "v"}{l}*kernel{l}{j}')
components.append('jetError uR uC uS uD vR vC vS vD eR eC eS eD')
out.append(f'theorem jet_product_expansion {args} :\n    {product} =\n    '+'+\n    '.join(components)+' := by\n  simp only [jet,jetB,jetError,topKernel,'+','.join('kernel'+l+str(j) for j in (2,3) for l in letters)+']\n  ring\n')
out.append('end\nend ToroidalQueens23\n')
(root/'formal/ToroidalQueens23/Expansion.lean').write_text('\n'.join(out),encoding='utf-8')

