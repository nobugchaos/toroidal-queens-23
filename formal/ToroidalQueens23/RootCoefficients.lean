import ToroidalQueens23.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Support


open scoped Polynomial
open Polynomial

namespace ToroidalQueens23

noncomputable section

def rootPolynomial (s : Finset F) : F[X] := ∏ a ∈ s, (X-C a)
def reversedRoots (s : Finset F) : F[X] := ∏ a ∈ s, (1-C a*X)

theorem rootPolynomial_degree (s : Finset F) : (rootPolynomial s).natDegree = s.card :=
  Polynomial.natDegree_finsetProd_X_sub_C_eq_card s id

theorem reflected_roots (s : Finset F) :
    (rootPolynomial s).reflect s.card = reversedRoots s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rootPolynomial,reversedRoots]
  | @insert a s ha ih =>
    simp only [rootPolynomial,reversedRoots,Finset.prod_insert ha,Finset.card_insert_of_notMem ha] at *
    rw [show s.card+1 = 1+s.card by omega,
      Polynomial.reflect_mul _ _ (by simp) (by rw [← rootPolynomial,rootPolynomial_degree]),ih]
    simp [Polynomial.reflect_sub,Polynomial.reflect_one_X,Polynomial.reflect_C]

theorem reversed_roots_coeff_zero (s : Finset F) : (reversedRoots s).coeff 0 = 1 := by
  simp [reversedRoots,Polynomial.coeff_zero_prod]

theorem linear_reversed_coeff (p : F[X]) (a : F) (n : Nat) :
    ((1-C a*X)*p).coeff (n+1) = p.coeff (n+1)-a*p.coeff n := by
  simp only [sub_mul,one_mul,mul_assoc,Polynomial.coeff_sub,
    Polynomial.coeff_C_mul,Polynomial.coeff_X_mul]

theorem reversed_roots_coeff_one (s : Finset F) :
    (reversedRoots s).coeff 1 = -∑ a ∈ s, a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reversedRoots,Polynomial.coeff_one]
  | @insert a s ha ih =>
    rw [reversedRoots,Finset.prod_insert ha,← reversedRoots,linear_reversed_coeff,
      reversed_roots_coeff_zero,ih,Finset.sum_insert ha]
    ring

theorem reversed_roots_coeff_two (s : Finset F) :
    2*(reversedRoots s).coeff 2 = (∑ a ∈ s, a)^2-∑ a ∈ s, a^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reversedRoots,Polynomial.coeff_one]
  | @insert a s ha ih =>
    rw [reversedRoots,Finset.prod_insert ha,← reversedRoots,linear_reversed_coeff,
      reversed_roots_coeff_one,Finset.sum_insert ha,Finset.sum_insert ha]
    calc
      2*((reversedRoots s).coeff 2-a*(-∑ x ∈ s, x)) =
        2*(reversedRoots s).coeff 2+2*a*(∑ x ∈ s, x) := by ring
      _ = (a+∑ x ∈ s, x)^2-(a^2+∑ x ∈ s, x^2) := by rw [ih]; ring

theorem rootPolynomial_coeff_reverse (s : Finset F) (j : Nat) (hj : j ≤ s.card) :
    (rootPolynomial s).coeff (s.card-j) = (reversedRoots s).coeff j := by
  rw [← reflected_roots,Polynomial.coeff_reflect,Polynomial.revAt_le hj]

theorem rootPolynomial_coeffs_eleven (s : Finset F) (hc : s.card = 11)
    (hs : ∑ a ∈ s, a = 0) :
    (rootPolynomial s).coeff 11 = 1 ∧ (rootPolynomial s).coeff 10 = 0 ∧
    (rootPolynomial s).coeff 9 = (reversedRoots s).coeff 2 ∧
    (rootPolynomial s).coeff 8 = (reversedRoots s).coeff 3 := by
  have h0 := rootPolynomial_coeff_reverse s 0 (by omega)
  have h1 := rootPolynomial_coeff_reverse s 1 (by omega)
  have h2 := rootPolynomial_coeff_reverse s 2 (by omega)
  have h3 := rootPolynomial_coeff_reverse s 3 (by omega)
  simp only [hc,Nat.sub_zero] at h0 h1 h2 h3
  simp only [reversed_roots_coeff_zero,reversed_roots_coeff_one,hs,neg_zero] at h0 h1
  exact ⟨h0,h1,h2,h3⟩

def rootTail (s : Finset F) : F[X] := rootPolynomial s-
  (X^11+C ((reversedRoots s).coeff 2)*X^9+C ((reversedRoots s).coeff 3)*X^8)

theorem rootTail_degree (s : Finset F) (hc : s.card = 11) (hs : ∑ a ∈ s, a = 0) :
    (rootTail s).natDegree ≤ 7 := by
  obtain ⟨h11,h10,h9,h8⟩ := rootPolynomial_coeffs_eleven s hc hs
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn11 : n ≤ 11
  · have he : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by omega
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [rootTail,Polynomial.coeff_C_mul_X_pow,h11,h10,h9,h8]
  · have hz : (rootPolynomial s).coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [rootPolynomial_degree,hc]
      omega
    have h8n : n ≠ 8 := by omega
    have h9n : n ≠ 9 := by omega
    have h11n : n ≠ 11 := by omega
    simp [rootTail,Polynomial.coeff_C_mul_X_pow,hz,h8n,h9n,h11n]

theorem root_expansion (s : Finset F) : rootPolynomial s =
    X^11+C ((reversedRoots s).coeff 2)*X^9+C ((reversedRoots s).coeff 3)*X^8+rootTail s := by
  unfold rootTail
  ring

end
end ToroidalQueens23

