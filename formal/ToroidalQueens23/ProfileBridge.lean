import ToroidalQueens23.Masks
import ToroidalQueens23.RootCoefficients

set_option maxHeartbeats 3000000

open scoped Polynomial

namespace ToroidalQueens23
noncomputable section

def maskPrefix (m : Nat) : Nat → Finset F
  | 0 => ∅
  | n+1 => if m.testBit n then insert (n : F) (maskPrefix m n) else maskPrefix m n

theorem mem_maskPrefix (m n : Nat) (x : F) :
    x ∈ maskPrefix m n ↔ ∃ i < n, m.testBit i = true ∧ (i : F) = x := by
  induction n with
  | zero => simp [maskPrefix]
  | succ n ih =>
    simp only [maskPrefix]
    split
    · rename_i hn
      rw [Finset.mem_insert,ih]
      constructor
      · rintro (rfl | ⟨i,hi,hb,hx⟩)
        · exact ⟨n,by omega,hn,rfl⟩
        · exact ⟨i,by omega,hb,hx⟩
      · rintro ⟨i,hi,hb,hx⟩
        by_cases e : i = n
        · left; simpa [e] using hx.symm
        · right; exact ⟨i,by omega,hb,hx⟩
    · rename_i hn
      rw [ih]
      constructor
      · rintro ⟨i,hi,hb,hx⟩; exact ⟨i,by omega,hb,hx⟩
      · rintro ⟨i,hi,hb,hx⟩
        refine ⟨i,?_,hb,hx⟩
        by_contra h
        have e : i = n := by omega
        subst i
        exact hn hb

theorem maskPrefix_fresh (m n : Nat) (hn : n < 23) :
    (n : F) ∉ maskPrefix m n := by
  rintro h
  obtain ⟨i,hi,_,he⟩ := (mem_maskPrefix m n (n : F)).mp h
  have hval := congrArg ZMod.val he
  have hi23 : i < 23 := by omega
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hi23,Nat.mod_eq_of_lt hn] at hval
  omega

theorem state_coefficients (m n : Nat) (hn : n ≤ 23) :
    (coefficientState m n).first = (reversedRoots (maskPrefix m n)).coeff 1 ∧
    (coefficientState m n).second = (reversedRoots (maskPrefix m n)).coeff 2 ∧
    (coefficientState m n).third = (reversedRoots (maskPrefix m n)).coeff 3 := by
  induction n with
  | zero => simp [coefficientState,initialState,maskPrefix,reversedRoots,Polynomial.coeff_one]
  | succ n ih =>
    have ih := ih (by omega)
    simp only [coefficientState,maskPrefix]
    split
    · have hf := maskPrefix_fresh m n (by omega)
      have hp : reversedRoots (insert (n : F) (maskPrefix m n)) =
          (1-Polynomial.C (n : F)*Polynomial.X)*reversedRoots (maskPrefix m n) := by
        simp only [reversedRoots,Finset.prod_insert hf]
      rw [hp]
      simp only [linear_reversed_coeff,reversed_roots_coeff_zero,addRoot]
      simp [ih.1,ih.2.1,ih.2.2]
    · exact ih

theorem maskPrefix_full (v : BitVec 23) : maskPrefix v.toNat 23 = decodeMask v := by
  ext x
  rw [mem_maskPrefix]
  simp only [decodeMask,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,hb,hx⟩
    subst x
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt hi,BitVec.getLsbD] using hb
  · intro hb
    exact ⟨x.val,x.val_lt,by simpa [BitVec.getLsbD] using hb,by simp⟩

theorem encode_state_coefficients (s : Finset F) :
    (coefficientState (encodeMask s).toNat 23).first = (reversedRoots s).coeff 1 ∧
    (coefficientState (encodeMask s).toNat 23).second = (reversedRoots s).coeff 2 ∧
    (coefficientState (encodeMask s).toNat 23).third = (reversedRoots s).coeff 3 := by
  simpa only [maskPrefix_full,decode_encode] using state_coefficients (encodeMask s).toNat 23 (by omega)

theorem root_profile_complete (s : Finset F) (hc : s.card = 11)
    (hs : ∑ x ∈ s, x = 0) (h3 : (reversedRoots s).coeff 3 = 0) :
    (encodeMask s).toNat ∈ coefficientProfiles[((reversedRoots s).coeff 2).val]! := by
  obtain ⟨h1,h2,h3'⟩ := encode_state_coefficients s
  rw [← h2]
  apply profile_mask_complete
  · exact (encodeMask s).isLt
  · rw [← decode_card,decode_encode,hc]
  · rw [h1,reversed_roots_coeff_one,hs,neg_zero]
  · rw [h3',h3]

end
end ToroidalQueens23
