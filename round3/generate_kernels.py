"""Emit exact characteristic-free identities, subsequently proved by Lean ring.
This generator supplies expressions, never trusted proof certificates.
"""
from pathlib import Path
from math import comb

root = Path(__file__).resolve().parent.parent
out = ['import ToroidalQueens23.Lift', '', 'set_option maxHeartbeats 4000000',
       'set_option maxRecDepth 100000', '', 'namespace ToroidalQueens23',
       'noncomputable section', '', '''@[simp] theorem exponent_inj (a b i j : Nat) :
    exponent a b = exponent i j ↔ a = i ∧ b = j := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun d => d 0) h,
      by simpa using congrArg (fun d => d 1) h⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem term_monomial (c : F) (a b : Nat) :
    MvPolynomial.C c * px^a * py^b = MvPolynomial.monomial (exponent a b) c := by
  simp [px,py,MvPolynomial.X_pow_eq_monomial,MvPolynomial.C_mul_monomial,exponent]

@[simp] theorem coeff_term (c : F) (a b i j : Nat) :
    (MvPolynomial.C c * px^a * py^b).coeff (exponent i j) =
      if a = i ∧ b = j then c else 0 := by
  rw [term_monomial,MvPolynomial.coeff_monomial]
  simp [eq_comm,exponent_inj]
''']

data = [('topKernel',(11,11,11,11))]
for j in (2,3):
    for k,t in enumerate('RCSD'):
        deg = [11]*4
        deg[k]-=j
        data.append((f'kernel{t}{j}',tuple(deg)))
data.append(('diagonalKernel10',(0,0,10,10)))

for name,(a,b,c,d) in data:
    coeff = {}
    for k in range(c+1):
        for l in range(d+1):
            ex = (a+c+d-k-l,b+k+l)
            coeff[ex] = coeff.get(ex,0)+comb(c,k)*comb(d,l)*(-1)**l
    terms = [(i,j,v) for (i,j),v in sorted(coeff.items(),reverse=True) if v]
    out.append(f'def {name} : Poly := px^{a}*py^{b}*ps^{c}*pd^{d}\n')
    expansion = '+\n    '.join(f'MvPolynomial.C (({v} : Int) : F)*px^{i}*py^{j}' for i,j,v in terms)
    out.append(f'theorem {name}_expansion : {name} =\n    {expansion} := by\n  simp only [{name},ps,pd,map_intCast]\n  ring\n')
    positions = [(22,20),(21,21),(20,22),(22,19),(21,20),(20,21),(19,22)]
    if name=='topKernel':
        negatives = '\n'.join(f'  have hn{k} : ¬ ({a0} = i ∧ {b0} = j) := by omega' for k,(a0,b0,v) in enumerate(terms))
        out.append(f'theorem {name}_high_zero (i j : Nat) (h : i+j < 44) :\n    {name}.coeff (exponent i j) = 0 := by\n  rw [{name}_expansion]\n{negatives}\n  simp only [MvPolynomial.coeff_add,coeff_term,'+', '.join(f'if_neg hn{k}' for k in range(len(terms)))+',add_zero]\n')
    elif name=='diagonalKernel10':
        out.append(f'theorem {name}_coefficient : {name}.coeff (exponent 10 10) = 1 := by\n  rw [{name}_expansion]\n  simp only [MvPolynomial.coeff_add,coeff_term]\n  norm_num\n  decide\n')
    else:
        # Generic coefficient formula, simplifies fixed positions without recompiling expansions.
        out.append(f'theorem {name}_coefficient (i j : Nat) :\n    {name}.coeff (exponent i j) =\n    '+ '+\n    '.join(f'(if {a0} = i ∧ {b0} = j then (({v}:Int):F) else 0)' for a0,b0,v in terms)+f' := by\n  rw [{name}_expansion]\n  simp only [MvPolynomial.coeff_add,coeff_term]\n')

out += ['end','end ToroidalQueens23','']
path = root/'formal/ToroidalQueens23/Kernels.lean'
path.write_text('\n'.join(out),encoding='utf-8')
print(path)



