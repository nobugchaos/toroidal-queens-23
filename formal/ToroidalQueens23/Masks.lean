import ToroidalQueens23.ProfileEnumeration
import Mathlib.Algebra.BigOperators.Fin

namespace ToroidalQueens23

def vectorOfFn (f : Fin 23 → Bool) : BitVec 23 :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

theorem vectorOfFn_bit (f : Fin 23 → Bool) (i : Fin 23) :
    (vectorOfFn f).getLsbD i.val = f i := by
  simp only [vectorOfFn,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  fin_cases i <;> rfl

def decodeMask (v : BitVec 23) : Finset F := Finset.univ.filter (fun x => v.getLsbD x.val)
noncomputable def encodeMask (s : Finset F) : BitVec 23 := by
  classical
  exact vectorOfFn (fun i => decide ((show F from i) ∈ s))

theorem encodeMask_bit (s : Finset F) (x : F) :
    (encodeMask s).getLsbD x.val = decide (x ∈ s) := by
  classical
  exact vectorOfFn_bit _ x

theorem decode_encode (s : Finset F) : decodeMask (encodeMask s) = s := by
  ext x
  simp [decodeMask,encodeMask_bit]

theorem countBits_range (m n : Nat) : countBits m n =
    ∑ i ∈ Finset.range n, if m.testBit i then 1 else 0 := by
  induction n with
  | zero => simp [countBits]
  | succ n ih => simp only [countBits,Finset.sum_range_succ,ih]

theorem decode_card (v : BitVec 23) : (decodeMask v).card = countBits v.toNat 23 := by
  rw [countBits_range]
  change ((Finset.univ : Finset (Fin 23)).filter (fun i => v.getLsbD i.val)).card = _
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if v.toNat.testBit i then 1 else 0) 23

theorem cpop_countBits (v : BitVec 23) : v.cpop.toNat = countBits v.toNat 23 := by
  rw [BitVec.toNat_cpop]
  have h (n : Nat) : v.cpopNatRec n 0 = countBits v.toNat n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [BitVec.cpopNatRec_succ,BitVec.cpopNatRec_eq,ih]
      simp [countBits,BitVec.getLsbD,Bool.toNat]
  exact h 23

theorem nonzero_bit (v : BitVec 23) : v ≠ 0 ↔ ∃ i : Fin 23, v.getLsbD i.val = true := by
  constructor
  · intro h
    by_contra hn
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh : v.getLsbD i ≠ true := by
      intro e
      exact hn ⟨⟨i,hi⟩,e⟩
    simpa using Bool.eq_false_of_not_eq_true hh
  · rintro ⟨i,hi⟩ e
    simp [e] at hi

end ToroidalQueens23
