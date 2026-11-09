import ToroidalQueens23.Masks
import Mathlib.Data.List.Count

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace ToroidalQueens23

def halfMask (s : BitVec 23) : BitVec 23 :=
  vectorOfFn (fun i => s.getLsbD ((2*(show F from i)).val))

def allowedMask (c h : BitVec 23) (d : Fin 23) : BitVec 23 :=
  ~~~(c.rotateLeft d.val) &&& ~~~(h.rotateLeft ((12*d.val)%23))

def allowedList (c h : BitVec 23) : List (BitVec 23) := List.ofFn (allowedMask c h)

def requiredCount (r : BitVec 23) (a : List (BitVec 23)) : Nat :=
  a.countP (fun v => (~~~r &&& v) != 0)

def checkProfileCover (b : Nat) : Bool :=
  let rows := coefficientProfiles[b]!
  let sums := coefficientProfiles[(2*b)%23]!
  rows.all fun c =>
    sums.all fun s =>
      let a := allowedList (BitVec.ofNat 23 c) (halfMask (BitVec.ofNat 23 s))
      rows.all fun r => decide (12 ≤ requiredCount (BitVec.ofNat 23 r) a)

/-- All groups are checked directly, without a scaling or symmetry reduction. -/
theorem all_profile_covers_checked : ∀ b : Fin 23, checkProfileCover b.val = true := by
  native_decide

#print axioms all_profile_covers_checked

end ToroidalQueens23
