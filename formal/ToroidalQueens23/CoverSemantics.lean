import ToroidalQueens23.CoverCheck

set_option maxHeartbeats 3000000

namespace ToroidalQueens23

theorem rotate_index_table : ∀ d r : F,
    (if r.val < d.val then 23-d.val+r.val else r.val-d.val) = (r-d).val := by
  decide

theorem rotate_bit (v : BitVec 23) (d r : F) :
    (v.rotateLeft d.val).getLsbD r.val = v.getLsbD (r-d).val := by
  rw [BitVec.getLsbD_rotateLeft,← rotate_index_table d r]
  simp only [Nat.mod_eq_of_lt d.val_lt,decide_eq_true r.val_lt,Bool.true_and]
  split_ifs <;> rfl

theorem twelve_val_table : ∀ d : F, (12*d).val = (12*d.val)%23 := by decide

theorem halfMask_bit (s : BitVec 23) (r : F) :
    (halfMask s).getLsbD r.val = s.getLsbD (2*r).val := vectorOfFn_bit _ r

theorem allowedMask_bit (c s : BitVec 23) (d r : F) :
    (allowedMask c (halfMask s) d).getLsbD r.val =
      (!c.getLsbD (r-d).val && !s.getLsbD (2*r-d).val) := by
  have he : 2*(r-12*d) = 2*r-d := by
    have h : (2 : F)*12 = 1 := by decide
    calc
      2*(r-12*d) = 2*r-(2*12)*d := by ring
      _ = 2*r-d := by rw [h,one_mul]
  simp only [allowedMask,BitVec.getLsbD_and,BitVec.getLsbD_not,
    decide_eq_true r.val_lt,Bool.true_and]
  change (!(c.rotateLeft d.val).getLsbD r.val &&
    !((halfMask s).rotateLeft ((12*d.val)%23)).getLsbD r.val) = _
  rw [rotate_bit,← twelve_val_table d,rotate_bit,halfMask_bit,he]

def neededDifferences (R C S : Finset F) : Finset F :=
  Finset.univ.filter (fun d => ∃ r : F, r ∉ R ∧ r-d ∉ C ∧ 2*r-d ∉ S)

theorem countP_sum {α : Type*} (p : α → Bool) (l : List α) :
    l.countP p = (l.map (fun x => if p x then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.countP_cons,List.map_cons,List.sum_cons,ih]; omega

theorem uncovered_bit_iff (R C S : Finset F) (d : F) :
    (~~~(encodeMask R) &&& allowedMask (encodeMask C) (halfMask (encodeMask S)) d) ≠ 0 ↔
      ∃ r : F, r ∉ R ∧ r-d ∉ C ∧ 2*r-d ∉ S := by
  rw [nonzero_bit]
  change (∃ r : F, (~~~(encodeMask R) &&&
    allowedMask (encodeMask C) (halfMask (encodeMask S)) d).getLsbD r.val = true) ↔ _
  apply exists_congr
  intro r
  rw [BitVec.getLsbD_and,BitVec.getLsbD_not,allowedMask_bit,
    encodeMask_bit R r,encodeMask_bit C (r-d),encodeMask_bit S (2*r-d)]
  simp [r.val_lt]

theorem requiredCount_card (R C S : Finset F) :
    requiredCount (encodeMask R) (allowedList (encodeMask C) (halfMask (encodeMask S))) =
      (neededDifferences R C S).card := by
  classical
  unfold requiredCount allowedList
  rw [countP_sum,List.map_ofFn,List.sum_ofFn]
  rw [neededDifferences,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro d _
  change (if (~~~(encodeMask R) &&& allowedMask (encodeMask C) (halfMask (encodeMask S)) d) != 0
    then 1 else 0) = _
  have he := uncovered_bit_iff R C S (show F from d)
  simp only [Function.comp_apply,bne_iff_ne,he]

theorem profile_cover_lower_bound (b : F) (R C S : Finset F)
    (hr : (encodeMask R).toNat ∈ coefficientProfiles[b.val]!)
    (hc : (encodeMask C).toNat ∈ coefficientProfiles[b.val]!)
    (hs : (encodeMask S).toNat ∈ coefficientProfiles[(2*b).val]!) :
    12 ≤ (neededDifferences R C S).card := by
  have h := all_profile_covers_checked b
  change checkProfileCover b.val = true at h
  dsimp only [checkProfileCover] at h
  have ht : (2*b).val = (2*b.val)%23 := by
    rw [ZMod.val_mul]
    rfl
  rw [← ht] at h
  have h := (List.all_eq_true.mp ((List.all_eq_true.mp ((List.all_eq_true.mp h) _ hc)) _ hs)) _ hr
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq,decide_eq_true_eq,requiredCount_card] using h

end ToroidalQueens23
