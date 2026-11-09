import ToroidalQueens23.Equations

set_option maxHeartbeats 4000000

namespace ToroidalQueens23
noncomputable section

def rowSet (s : Finset Square) : Finset F := s.image Prod.fst
def colSet (s : Finset Square) : Finset F := s.image Prod.snd
def sumSet (s : Finset Square) : Finset F := s.image (fun q => q.1+q.2)
def diffSet (s : Finset Square) : Finset F := s.image (fun q => q.1-q.2)

theorem projection_cards (s : Finset Square) (h : Independent s) :
    (rowSet s).card = s.card ∧ (colSet s).card = s.card ∧
    (sumSet s).card = s.card ∧ (diffSet s).card = s.card :=
  ⟨Finset.card_image_iff.mpr (row_inj_on h),Finset.card_image_iff.mpr (col_inj_on h),
   Finset.card_image_iff.mpr (sum_inj_on h),Finset.card_image_iff.mpr (diff_inj_on h)⟩

theorem projection_sums (s : Finset Square) (h : Independent s)
    (hr : ∑ q ∈ s, q.1 = 0) (hc : ∑ q ∈ s, q.2 = 0) :
    (∑ x ∈ rowSet s, x) = 0 ∧ (∑ x ∈ colSet s, x) = 0 ∧
    (∑ x ∈ sumSet s, x) = 0 ∧ (∑ x ∈ diffSet s, x) = 0 := by
  simp only [rowSet,colSet,sumSet,diffSet,
    Finset.sum_image (row_inj_on h),Finset.sum_image (col_inj_on h),
    Finset.sum_image (sum_inj_on h),Finset.sum_image (diff_inj_on h),
    Finset.sum_add_distrib,Finset.sum_sub_distrib,hr,hc,zero_add,sub_zero,and_self]

def coverPolynomial (R C S D : Finset F) : Poly :=
  liftPolynomial px (rootPolynomial R)*liftPolynomial py (rootPolynomial C)*
  liftPolynomial ps (rootPolynomial S)*liftPolynomial pd (rootPolynomial D)

theorem coverPolynomial_vanishes (s : Finset Square) (h : Dominating s) (x y : F) :
    MvPolynomial.eval ![x,y] (coverPolynomial (rowSet s) (colSet s) (sumSet s) (diffSet s)) = 0 := by
  obtain ⟨q,hq,hcover⟩ := h (x,y)
  simp only [coverPolynomial,map_mul]
  rcases hcover with hr | hc | hs | hd
  · have hz := eval_lift_root px (rowSet s) x y (by
      simp only [px,MvPolynomial.eval_X,Matrix.cons_val_zero]
      exact Finset.mem_image.mpr ⟨q,hq,hr⟩)
    rw [hz]; ring
  · have hz := eval_lift_root py (colSet s) x y (by
      simp only [py,MvPolynomial.eval_X,Matrix.cons_val_one,Matrix.cons_val_zero]
      exact Finset.mem_image.mpr ⟨q,hq,hc⟩)
    rw [hz]; ring
  · have hz := eval_lift_root ps (sumSet s) x y (by
      simp only [ps,px,py,map_add,MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one]
      exact Finset.mem_image.mpr ⟨q,hq,hs⟩)
    rw [hz]; ring
  · have hz := eval_lift_root pd (diffSet s) x y (by
      simp only [pd,px,py,map_sub,MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one]
      exact Finset.mem_image.mpr ⟨q,hq,hd⟩)
    rw [hz]; ring

def rootU (s : Finset F) : F := (reversedRoots s).coeff 2
def rootV (s : Finset F) : F := (reversedRoots s).coeff 3

theorem lift_as_jet (z : Poly) (s : Finset F) :
    liftPolynomial z (rootPolynomial s) = jet z (rootU s) (rootV s) (liftPolynomial z (rootTail s)) := by
  rw [root_expansion]
  simp [liftPolynomial,jet,jetB,rootU,rootV,add_assoc]

theorem cover_constraints (R C S D : Finset F)
    (hc : R.card = 11 ∧ C.card = 11 ∧ S.card = 11 ∧ D.card = 11)
    (hs : (∑ x ∈ R, x) = 0 ∧ (∑ x ∈ C, x) = 0 ∧
      (∑ x ∈ S, x) = 0 ∧ (∑ x ∈ D, x) = 0)
    (hz : ∀ x y : F, MvPolynomial.eval ![x,y] (coverPolynomial R C S D) = 0) :
    rootU R = rootU C ∧ rootU S = rootU D ∧
    rootV R = 0 ∧ rootV C = 0 ∧ rootV S = 0 ∧ rootV D = 0 := by
  have heR := (liftPolynomial_degree px px_degree (rootTail R)).trans (rootTail_degree R hc.1 hs.1)
  have heC := (liftPolynomial_degree py py_degree (rootTail C)).trans (rootTail_degree C hc.2.1 hs.2.1)
  have heS := (liftPolynomial_degree ps ps_degree (rootTail S)).trans (rootTail_degree S hc.2.2.1 hs.2.2.1)
  have heD := (liftPolynomial_degree pd pd_degree (rootTail D)).trans (rootTail_degree D hc.2.2.2 hs.2.2.2)
  have hj : ∀ x y : F, MvPolynomial.eval ![x,y]
      ((jet px (rootU R) (rootV R) (liftPolynomial px (rootTail R)))*
       (jet py (rootU C) (rootV C) (liftPolynomial py (rootTail C)))*
       (jet ps (rootU S) (rootV S) (liftPolynomial ps (rootTail S)))*
       (jet pd (rootU D) (rootV D) (liftPolynomial pd (rootTail D)))) = 0 := by
    simpa only [coverPolynomial,lift_as_jet] using hz
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := jet_equations _ _ _ _ _ _ _ _ _ _ _ _ heR heC heS heD hj
  obtain ⟨hRC,hSD⟩ := solve_quadratic_coefficients _ _ _ _ h0 h1
  exact ⟨hRC,hSD,solve_cubic_coefficients _ _ _ _ h2 h3 h4 h5⟩

theorem square_sum_identity (s : Finset Square) (h : Independent s) :
    (∑ x ∈ sumSet s, x^2)+(∑ x ∈ diffSet s, x^2) =
    2*((∑ x ∈ rowSet s, x^2)+(∑ x ∈ colSet s, x^2)) := by
  rw [sumSet,diffSet,rowSet,colSet,
    Finset.sum_image (sum_inj_on h),Finset.sum_image (diff_inj_on h),
    Finset.sum_image (row_inj_on h),Finset.sum_image (col_inj_on h),
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem quadratic_doubling (s : Finset Square) (h : Independent s)
    (hs : (∑ x ∈ rowSet s, x) = 0 ∧ (∑ x ∈ colSet s, x) = 0 ∧
      (∑ x ∈ sumSet s, x) = 0 ∧ (∑ x ∈ diffSet s, x) = 0)
    (hrc : rootU (rowSet s) = rootU (colSet s))
    (hsd : rootU (sumSet s) = rootU (diffSet s)) :
    rootU (sumSet s) = 2*rootU (rowSet s) := by
  have hR := reversed_roots_coeff_two (rowSet s)
  have hC := reversed_roots_coeff_two (colSet s)
  have hS := reversed_roots_coeff_two (sumSet s)
  have hD := reversed_roots_coeff_two (diffSet s)
  simp only [hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,zero_pow (by decide : 2 ≠ 0),zero_sub] at hR hC hS hD
  change 2*rootU (rowSet s) = _ at hR
  change 2*rootU (colSet s) = _ at hC
  change 2*rootU (sumSet s) = _ at hS
  change 2*rootU (diffSet s) = _ at hD
  have hi := square_sum_identity s h
  have hh : 2*(rootU (sumSet s)+rootU (diffSet s)) =
      2*(2*(rootU (rowSet s)+rootU (colSet s))) := by
    linear_combination hS+hD-2*hR-2*hC-hi
  have htwo : (2 : F) ≠ 0 := by decide
  have hh := mul_left_cancel₀ htwo hh
  rw [← hrc,← hsd] at hh
  have he : 2*rootU (sumSet s) = 2*(2*rootU (rowSet s)) := by linear_combination hh
  exact mul_left_cancel₀ htwo he

end
end ToroidalQueens23
