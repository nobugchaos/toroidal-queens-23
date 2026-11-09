from pathlib import Path
from itertools import combinations
from math import comb
root=Path(__file__).resolve().parent.parent
out=['import ToroidalQueens23.Geometry','','set_option maxHeartbeats 4000000',
     'set_option maxRecDepth 100000','','namespace ToroidalQueens23','noncomputable section','', '''
def tailTen (s : Finset F) : Polynomial F := rootPolynomial s-Polynomial.X^10

theorem tailTen_degree (s : Finset F) (hc : s.card = 10) : (tailTen s).natDegree ≤ 9 := by
  have hh := rootPolynomial_coeff_reverse s 0 (by omega)
  simp only [hc,Nat.sub_zero,reversed_roots_coeff_zero] at hh
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases he : n = 10
  · subst n
    simp [tailTen,hh]
  · have hz : (rootPolynomial s).coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [rootPolynomial_degree,hc]
      omega
    simp [tailTen,hz,he]

theorem lift_ten (z : Poly) (s : Finset F) :
    liftPolynomial z (rootPolynomial s) = z^10+liftPolynomial z (tailTen s) := by
  have hh : rootPolynomial s = Polynomial.X^10+tailTen s := by unfold tailTen; ring
  rw [hh]
  simp [liftPolynomial]

def topTen : Poly := px^10*py^10*ps^10*pd^10
''']
terms=[(30-2*k,10+2*k,comb(10,k)*(-1)**k) for k in range(11)]
out.append('theorem topTen_expansion : topTen =\n    '+ '+\n    '.join(f'MvPolynomial.C (({v}:Int):F)*px^{i}*py^{j}' for i,j,v in terms)+''' := by
  simp only [topTen,ps,pd,map_intCast]
  ring

theorem topTen_coefficient : topTen.coeff (exponent 20 20) = 1 := by
  rw [topTen_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]
  norm_num <;> decide
''')
names=['px','py','ps','pd'];ls='RCSD'
terms=[]
for k in (1,2,3,4):
 for inds in combinations(range(4),k):
  fac=[f'{z}^10' for z in names]
  b=[f'(degree_pow_bound {z}_degree 10)' for z in names]
  for t in inds:fac[t]='e'+ls[t];b[t]='he'+ls[t]
  terms.append(('*'.join(fac),b))
out.append('def tenError (eR eC eS eD : Poly) : Poly :=\n    '+'+\n    '.join(e for e,_ in terms)+'\n')
out.append('''theorem tenError_degree (eR eC eS eD : Poly)
    (heR : eR.totalDegree ≤ 9) (heC : eC.totalDegree ≤ 9)
    (heS : eS.totalDegree ≤ 9) (heD : eD.totalDegree ≤ 9) :
    (tenError eR eC eS eD).totalDegree ≤ 39 := by
  unfold tenError''')
def degree_tree(ts,indent='  '):
 if len(ts)==1:
  return [indent+'exact (degree_four '+' '.join(ts[0][1])+').trans (by decide)']
 a=degree_tree(ts[:-1],indent+'  ');b=degree_tree(ts[-1:],indent+'  ')
 a[0]=indent+'· '+a[0].lstrip();b[0]=indent+'· '+b[0].lstrip()
 return [indent+'apply degree_add_bound']+a+b
out+=degree_tree(terms)
out.append('''
theorem ten_product_expansion (eR eC eS eD : Poly) :
    (px^10+eR)*(py^10+eC)*(ps^10+eS)*(pd^10+eD) =
      topTen+tenError eR eC eS eD := by
  simp only [topTen,tenError]
  ring

theorem cover_ten_degree (R C S D : Finset F)
    (hR : R.card = 10) (hC : C.card = 10) (hS : S.card = 10) (hD : D.card = 10) :
    (coverPolynomial R C S D).totalDegree ≤ 40 := by
  have hR' := liftPolynomial_degree px px_degree (rootPolynomial R)
  have hC' := liftPolynomial_degree py py_degree (rootPolynomial C)
  have hS' := liftPolynomial_degree ps ps_degree (rootPolynomial S)
  have hD' := liftPolynomial_degree pd pd_degree (rootPolynomial D)
  simp only [rootPolynomial_degree,hR,hC,hS,hD] at hR' hC' hS' hD'
  exact degree_four hR' hC' hS' hD'

theorem cover_ten_coefficient (R C S D : Finset F)
    (hR : R.card = 10) (hC : C.card = 10) (hS : S.card = 10) (hD : D.card = 10) :
    (coverPolynomial R C S D).coeff (exponent 20 20) = 1 := by
  have heR := (liftPolynomial_degree px px_degree (tailTen R)).trans (tailTen_degree R hR)
  have heC := (liftPolynomial_degree py py_degree (tailTen C)).trans (tailTen_degree C hC)
  have heS := (liftPolynomial_degree ps ps_degree (tailTen S)).trans (tailTen_degree S hS)
  have heD := (liftPolynomial_degree pd pd_degree (tailTen D)).trans (tailTen_degree D hD)
  have he : (tenError (liftPolynomial px (tailTen R)) (liftPolynomial py (tailTen C))
      (liftPolynomial ps (tailTen S)) (liftPolynomial pd (tailTen D))).coeff (exponent 20 20) = 0 := by
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    have hb := tenError_degree _ _ _ _ heR heC heS heD
    change _ < (exponent 20 20).sum (fun _ n => n)
    rw [exponent_degree,exponent_zero,exponent_one]
    omega
  rw [coverPolynomial,lift_ten,lift_ten,lift_ten,lift_ten,ten_product_expansion,
    MvPolynomial.coeff_add,topTen_coefficient,he,add_zero]

theorem cover_vanishes_of_subsets (s : Finset Square) (hd : Dominating s)
    (R C S D : Finset F) (hR : rowSet s ⊆ R) (hC : colSet s ⊆ C)
    (hS : sumSet s ⊆ S) (hD : diffSet s ⊆ D) (x y : F) :
    MvPolynomial.eval ![x,y] (coverPolynomial R C S D) = 0 := by
  obtain ⟨q,hq,hh⟩ := hd (x,y)
  simp only [coverPolynomial,map_mul]
  rcases hh with hr | hc | hs | hd
  · have hz := eval_lift_root px R x y (by
      simp only [px,MvPolynomial.eval_X,Matrix.cons_val_zero]
      exact hR (Finset.mem_image.mpr ⟨q,hq,hr⟩))
    rw [hz]; ring
  · have hz := eval_lift_root py C x y (by
      simp only [py,MvPolynomial.eval_X,Matrix.cons_val_one,Matrix.cons_val_zero]
      exact hC (Finset.mem_image.mpr ⟨q,hq,hc⟩))
    rw [hz]; ring
  · have hz := eval_lift_root ps S x y (by
      simp only [ps,px,py,map_add,MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one]
      exact hS (Finset.mem_image.mpr ⟨q,hq,hs⟩))
    rw [hz]; ring
  · have hz := eval_lift_root pd D x y (by
      simp only [pd,px,py,map_sub,MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one]
      exact hD (Finset.mem_image.mpr ⟨q,hq,hd⟩))
    rw [hz]; ring

theorem pad_ten (s : Finset F) (hs : s.card ≤ 10) : ∃ t : Finset F, s ⊆ t ∧ t.card = 10 := by
  obtain ⟨t,ht,_,hc⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ s) hs (by decide : 10 ≤ (Finset.univ : Finset F).card)
  exact ⟨t,ht,hc⟩

theorem dominating_card_at_least_eleven (s : Finset Square) (hd : Dominating s) : 11 ≤ s.card := by
  by_contra h
  have hc : s.card ≤ 10 := by omega
  obtain ⟨R,hR,hRc⟩ := pad_ten (rowSet s) ((Finset.card_image_le).trans hc)
  obtain ⟨C,hC,hCc⟩ := pad_ten (colSet s) ((Finset.card_image_le).trans hc)
  obtain ⟨S,hS,hSc⟩ := pad_ten (sumSet s) ((Finset.card_image_le).trans hc)
  obtain ⟨D,hD,hDc⟩ := pad_ten (diffSet s) ((Finset.card_image_le).trans hc)
  have hz := high_coefficient_zero (coverPolynomial R C S D)
    ((cover_ten_degree R C S D hRc hCc hSc hDc).trans (by decide))
    (cover_vanishes_of_subsets s hd R C S D hR hC hS hD) 20 20 (by decide) (by decide) (by decide)
  rw [cover_ten_coefficient R C S D hRc hCc hSc hDc] at hz
  exact one_ne_zero hz

end
end ToroidalQueens23
''')
(root/'formal/ToroidalQueens23/LowerTen.lean').write_text('\n'.join(out),encoding='utf-8')
