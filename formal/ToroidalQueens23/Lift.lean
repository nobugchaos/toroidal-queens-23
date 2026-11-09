import ToroidalQueens23.Grid
import ToroidalQueens23.RootCoefficients
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.MvPolynomial.CommRing

open scoped Polynomial

namespace ToroidalQueens23
noncomputable section

def liftPolynomial (z : Poly) : F[X] →+* Poly := Polynomial.eval₂RingHom MvPolynomial.C z

theorem lift_rootPolynomial (z : Poly) (s : Finset F) :
    liftPolynomial z (rootPolynomial s) = ∏ a ∈ s, (z-MvPolynomial.C a) := by
  simp [liftPolynomial,rootPolynomial,Polynomial.eval₂_finset_prod]

theorem liftPolynomial_degree (z : Poly) (hz : z.totalDegree ≤ 1) (p : F[X]) :
    (liftPolynomial z p).totalDegree ≤ p.natDegree := by
  conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro n hn
  have hn' : n ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)
  have hpow := MvPolynomial.totalDegree_pow z n
  have hmul := MvPolynomial.totalDegree_mul (MvPolynomial.C (p.coeff n)) (z^n)
  have hp : (z^n).totalDegree ≤ n := by simpa using hpow.trans (Nat.mul_le_mul_left n hz)
  have hm : (MvPolynomial.C (p.coeff n)*z^n).totalDegree ≤ p.natDegree :=
    hmul.trans (by simpa using hp.trans hn')
  simpa [liftPolynomial] using hm

def px : Poly := MvPolynomial.X 0
def py : Poly := MvPolynomial.X 1
def ps : Poly := px+py
def pd : Poly := px-py

theorem px_degree : px.totalDegree ≤ 1 := by simp [px]
theorem py_degree : py.totalDegree ≤ 1 := by simp [py]
theorem ps_degree : ps.totalDegree ≤ 1 := by
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le px_degree py_degree)
theorem pd_degree : pd.totalDegree ≤ 1 := by
  rw [pd,sub_eq_add_neg]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le px_degree (by simpa using py_degree))

theorem degree_four {a b c d : Poly} {ka kb kc kd : Nat}
    (ha : a.totalDegree ≤ ka) (hb : b.totalDegree ≤ kb)
    (hc : c.totalDegree ≤ kc) (hd : d.totalDegree ≤ kd) :
    (a*b*c*d).totalDegree ≤ ka+kb+kc+kd := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply add_le_add _ hd
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply add_le_add _ hc
  exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add ha hb)

theorem eval_lift_root (z : Poly) (s : Finset F) (x y : F)
    (h : MvPolynomial.eval ![x,y] z ∈ s) :
    MvPolynomial.eval ![x,y] (liftPolynomial z (rootPolynomial s)) = 0 := by
  rw [lift_rootPolynomial,MvPolynomial.eval_prod]
  apply Finset.prod_eq_zero h
  simp

end
end ToroidalQueens23
