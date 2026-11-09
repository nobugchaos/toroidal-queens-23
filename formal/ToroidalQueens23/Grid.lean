import ToroidalQueens23.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace ToroidalQueens23

noncomputable section

abbrev Poly := MvPolynomial (Fin 2) F

def exponent (a b : Nat) : Fin 2 →₀ Nat := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem exponent_zero (a b : Nat) : exponent a b 0 = a := by simp [exponent]
@[simp] theorem exponent_one (a b : Nat) : exponent a b 1 = b := by simp [exponent]

theorem exponent_ext (d : Fin 2 →₀ Nat) : exponent (d 0) (d 1) = d := by
  ext i
  fin_cases i <;> simp

theorem exponent_degree (d : Fin 2 →₀ Nat) : d.sum (fun _ n => n) = d 0+d 1 := by
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_two]
  · simp

def powerSum (n : Nat) : F := ∑ x : F, x^n

theorem powerSum_table : ∀ n : Fin 89,
    powerSum n = if 0 < n.val ∧ n.val % 22 = 0 then -1 else 0 := by
  native_decide

theorem powerSum_formula (n : Nat) (h : n < 89) :
    powerSum n = if 0 < n ∧ n % 22 = 0 then -1 else 0 :=
  powerSum_table ⟨n,h⟩

def weighted (a b : Nat) : Poly →+ F where
  toFun p := ∑ x : F, ∑ y : F,
    x^(22-a)*y^(22-b)*MvPolynomial.eval ![x,y] p
  map_zero' := by simp
  map_add' p q := by
    simp only [map_add,mul_add,Finset.sum_add_distrib]

theorem factor_double_sum {R : Type*} [CommSemiring R] [Fintype R]
    (c : R) (f g : R → R) :
    (∑ x : R, ∑ y : R, c*f x*g y) = c*(∑ x : R, f x)*(∑ y : R, g y) := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem weighted_monomial (a b : Nat) (d : Fin 2 →₀ Nat) (c : F) :
    weighted a b (MvPolynomial.monomial d c) =
      c * powerSum (22-a+d 0) * powerSum (22-b+d 1) := by
  have he (x y : F) : MvPolynomial.eval ![x,y] (MvPolynomial.monomial d c) =
      c*(x^(d 0)*y^(d 1)) := by
    rw [MvPolynomial.eval_monomial,
      Finsupp.prod_fintype d (fun i n => (![x,y] i)^n) (by intro i; simp),
      Fin.prod_univ_two]
    rfl
  change (∑ x : F, ∑ y : F,
    x^(22-a)*y^(22-b)*MvPolynomial.eval ![x,y] (MvPolynomial.monomial d c)) = _
  simp_rw [he]
  calc
    (∑ x : F, ∑ y : F, x^(22-a)*y^(22-b)*(c*(x^(d 0)*y^(d 1)))) =
      ∑ x : F, ∑ y : F, c*x^(22-a+d 0)*y^(22-b+d 1) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        simp only [pow_add]
        ring
    _ = c * powerSum (22-a+d 0) * powerSum (22-b+d 1) := by
      exact factor_double_sum c (fun x : F => x^(22-a+d 0)) (fun y : F => y^(22-b+d 1))

theorem isolate_exponents (a b i j : Nat)
    (ha : a ≤ 22) (hb : b ≤ 22) (hab : 22 < a+b) (hij : i+j ≤ 44) :
    powerSum (22-a+i)*powerSum (22-b+j) =
      if i = a ∧ j = b then 1 else 0 := by
  rw [powerSum_formula _ (by omega),powerSum_formula _ (by omega)]
  have hiff : (0 < 22-a+i ∧ (22-a+i)%22 = 0) ∧
      (0 < 22-b+j ∧ (22-b+j)%22 = 0) ↔ i = a ∧ j = b := by omega
  by_cases he : i = a ∧ j = b
  · obtain ⟨hei,hej⟩ := he
    subst i
    subst j
    rw [show 22-a+a = 22 by omega,show 22-b+b = 22 by omega]
    norm_num
  · by_cases h1 : 0 < 22-a+i ∧ (22-a+i)%22 = 0
    · have h2 : ¬ (0 < 22-b+j ∧ (22-b+j)%22 = 0) := fun h2 => he (hiff.mp ⟨h1,h2⟩)
      rw [ite_eq_right h2,mul_zero,ite_eq_right he]
    · rw [ite_eq_right h1,zero_mul,ite_eq_right he]

theorem coefficient_from_grid (p : Poly) (hdeg : p.totalDegree ≤ 44)
    (a b : Nat) (ha : a ≤ 22) (hb : b ≤ 22) (hab : 22 < a+b) :
    weighted a b p = p.coeff (exponent a b) := by
  calc
    weighted a b p = ∑ d ∈ p.support,
      weighted a b (MvPolynomial.monomial d (p.coeff d)) := by
        conv_lhs => rw [p.as_sum]
        simp only [map_sum]
    _ = ∑ d ∈ p.support, if d = exponent a b then p.coeff d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hbound : d 0+d 1 ≤ 44 := by
        have he := (MvPolynomial.le_totalDegree hd).trans hdeg
        simpa [exponent_degree] using he
      rw [weighted_monomial,mul_assoc,isolate_exponents a b (d 0) (d 1) ha hb hab hbound]
      have heq : (d 0 = a ∧ d 1 = b) ↔ d = exponent a b := by
        constructor
        · rintro ⟨h0,h1⟩
          rw [← exponent_ext d,h0,h1]
        · intro e
          simp [e]
      by_cases he : d = exponent a b
      · simp [he,heq]
      · simp [he,heq]
    _ = p.coeff (exponent a b) := by
      classical
      by_cases he : exponent a b ∈ p.support
      · simp [Finset.sum_ite_eq',he]
      · simp [Finset.sum_ite_eq',he,MvPolynomial.notMem_support_iff.mp he]

theorem high_coefficient_zero (p : Poly) (hdeg : p.totalDegree ≤ 44)
    (hz : ∀ x y : F, MvPolynomial.eval ![x,y] p = 0)
    (a b : Nat) (ha : a ≤ 22) (hb : b ≤ 22) (hab : 22 < a+b) :
    p.coeff (exponent a b) = 0 := by
  rw [← coefficient_from_grid p hdeg a b ha hb hab]
  simp [weighted,hz]

end
end ToroidalQueens23
