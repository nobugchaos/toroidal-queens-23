from pathlib import Path
root=Path(__file__).resolve().parent.parent
names='RCSD'
pos=[(22,20),(21,21),(20,22),(22,19),(21,20),(20,21),(19,22)]
out=['import ToroidalQueens23.Expansion','import Mathlib.Algebra.Field.ZMod','','set_option maxHeartbeats 4000000',
     'set_option maxRecDepth 100000','','namespace ToroidalQueens23','noncomputable section','']
# Exact kernel tables. Closed field arithmetic is proved by kernel decide.
from math import comb
for j in (2,3):
 for t,l in enumerate(names):
  ds=[11]*4;ds[t]-=j
  a,b,c,d=ds
  coeff={}
  for k in range(c+1):
   for h in range(d+1):
    ex=(a+c+d-k-h,b+k+h)
    coeff[ex]=coeff.get(ex,0)+comb(c,k)*comb(d,h)*(-1)**h
  for i,h in pos:
   out.append(f'@[simp] theorem kernel{l}{j}_{i}_{h} : kernel{l}{j}.coeff (exponent {i} {h}) = ({coeff.get((i,h),0)%23} : F) := by\n  rw [kernel{l}{j}_coefficient]\n  norm_num <;> decide\n')
out.append('''theorem jet_degree {z e : Poly} (hz : z.totalDegree ≤ 1) (he : e.totalDegree ≤ 7)
    (u v : F) : (jet z u v e).totalDegree ≤ 11 := by
  exact degree_add_bound (degree_pow_bound hz 11) ((jetB_degree hz he u v).trans (by decide))
''')
args='(uR uC uS uD vR vC vS vD : F) (eR eC eS eD : Poly)'
he='''    (heR : eR.totalDegree ≤ 7) (heC : eC.totalDegree ≤ 7)
    (heS : eS.totalDegree ≤ 7) (heD : eD.totalDegree ≤ 7)'''
par='uR uC uS uD vR vC vS vD eR eC eS eD'
product='(jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)'
out.append(f'''theorem jet_coeff_formula {args}
{he} (i j : Nat) (hlo : 40 < i+j) (hhi : i+j < 44) :
    ({product}).coeff (exponent i j) =
    '''+'+\n    '.join(f'{u}{l}*kernel{l}{k}.coeff (exponent i j)' for k,u in [(2,'u'),(3,'v')] for l in names)+f''' := by
  rw [jet_product_expansion]
  have he : (jetError {par}).coeff (exponent i j) = 0 := by
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    have hb := jetError_degree {par} heR heC heS heD
    change _ < (exponent i j).sum (fun _ n => n)
    rw [exponent_degree,exponent_zero,exponent_one]
    exact lt_of_le_of_lt hb hlo
  simp only [MvPolynomial.coeff_add,MvPolynomial.coeff_C_mul,
    topKernel_high_zero i j hhi,he,zero_add,add_zero]
''')
rows=[('h0',22,20,'uS+uD*22'),('h1',21,21,'uR*21+uC*2'),
      ('h2',22,19,'vR*8+vS*17+vD*17'),('h3',21,20,'vC*2+vS*7+vD*16'),
      ('h4',20,21,'vR*21+vS*16+vD*16'),('h5',19,22,'vC*15+vS*6+vD*17')]
out.append(f'''theorem jet_equations {args}
{he}
    (hz : ∀ x y : F, MvPolynomial.eval ![x,y] ({product}) = 0) :
    '''+' ∧\n    '.join(f'{expr} = 0' for _,_,_,expr in rows)+f''' := by
  have hdeg : ({product}).totalDegree ≤ 44 := by
    exact degree_four (jet_degree px_degree heR uR vR) (jet_degree py_degree heC uC vC)
      (jet_degree ps_degree heS uS vS) (jet_degree pd_degree heD uD vD)
''')
for h,i,j,expr in rows:
 out.append(f'''  have {h} : {expr} = 0 := by
    have hc := high_coefficient_zero ({product}) hdeg hz {i} {j} (by decide) (by decide) (by decide)
    rw [jet_coeff_formula {par} heR heC heS heD {i} {j} (by decide) (by decide)] at hc
    simpa using hc''')
out.append('  exact ⟨h0,h1,h2,h3,h4,h5⟩\n')
# arithmetic inverse for third coefficient matrix
M=[[8,0,17,17],[0,2,7,16],[21,0,16,16],[0,15,6,17]]
aug=[r[:]+[int(i==j) for j in range(4)] for i,r in enumerate(M)]
for k in range(4):
 pivot=next(i for i in range(k,4) if aug[i][k]%23)
 aug[k],aug[pivot]=aug[pivot],aug[k]
 inv=pow(aug[k][k],-1,23)
 aug[k]=[v*inv%23 for v in aug[k]]
 for i in range(4):
  if i!=k:
   v=aug[i][k];aug[i]=[(a-v*b)%23 for a,b in zip(aug[i],aug[k])]
inv=[r[4:] for r in aug]
vars=['vR','vC','vS','vD']
rowexpr=[expr for _,_,_,expr in rows[2:]]
out.append('theorem solve_cubic_coefficients (vR vC vS vD : F)\n'+
 '\n'.join(f'    (h{i} : {e} = 0)' for i,e in enumerate(rowexpr))+''' :
    vR = 0 ∧ vC = 0 ∧ vS = 0 ∧ vD = 0 := by''')
for k,v in enumerate(vars):
 cs=[sum(inv[k][i]*M[i][j] for i in range(4)) for j in range(4)]
 for j,c in enumerate(cs):
  out.append(f'  have h{k}{j} : ({c} : F) = {int(k==j)} := by decide')
 linear='+'.join(f'{cs[j]}*{vars[j]}' for j in range(4))
 combined='+'.join(f'{inv[k][i]}*({rowexpr[i]})' for i in range(4))
 out.append(f'''  have {v}_id : {v} = {combined} := by
    calc
      {v} = {linear} := by simp only [h{k}0,h{k}1,h{k}2,h{k}3,zero_mul,one_mul,add_zero,zero_add]
      _ = {combined} := by ring''')
out.append('  exact ⟨by simpa [h0,h1,h2,h3] using vR_id,by simpa [h0,h1,h2,h3] using vC_id,\n    by simpa [h0,h1,h2,h3] using vS_id,by simpa [h0,h1,h2,h3] using vD_id⟩\n')
out.append('''theorem solve_quadratic_coefficients (uR uC uS uD : F)
    (h0 : uS+uD*22 = 0) (h1 : uR*21+uC*2 = 0) : uR = uC ∧ uS = uD := by
  have h22 : (22 : F) = -1 := by decide
  have h21 : (21 : F) = -2 := by decide
  have h2 : (2 : F) ≠ 0 := by decide
  have hs : uS-uD = 0 := by simpa [h22,sub_eq_add_neg] using h0
  have hr : (uC-uR)*2 = 0 := by
    calc (uC-uR)*2 = uR*(-2)+uC*2 := by ring
         _ = 0 := by simpa [h21] using h1
  exact ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right h2)).symm,sub_eq_zero.mp hs⟩
''')
out+=['end','end ToroidalQueens23','']
(root/'formal/ToroidalQueens23/Equations.lean').write_text('\n'.join(out),encoding='utf-8')
