import ToroidalQueens23.ProfileData

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace ToroidalQueens23

structure CoefficientState where
  size : Nat
  first : F
  second : F
  third : F
deriving DecidableEq

def initialState : CoefficientState := ⟨0,0,0,0⟩

def addRoot (s : CoefficientState) (x : F) : CoefficientState :=
  ⟨s.size+1,s.first-x,s.second-x*s.first,s.third-x*s.second⟩

def coefficientState (m : Nat) : Nat → CoefficientState
  | 0 => initialState
  | n+1 => let s := coefficientState m n
    if m.testBit n then addRoot s n else s

def countBits (m : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => countBits m n + if m.testBit n then 1 else 0

theorem coefficientState_size (m n : Nat) : (coefficientState m n).size = countBits m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [coefficientState,countBits]
    split <;> simp_all [addRoot]

def checkProfileMask (m : Nat) : Bool :=
  if countBits m 23 = 11 then
    let s := coefficientState m 23
    if s.first == 0 && s.third == 0 then
      (coefficientProfiles[s.second.val]!).contains m
    else true
  else true

def scanRange (f : Nat → Bool) (base : Nat) : Nat → Bool
  | 0 => true
  | n+1 => f base && scanRange f (base+1) n

theorem scanRange_sound (f : Nat → Bool) (base n : Nat)
    (h : scanRange f base n = true) (i : Nat) (hlo : base ≤ i) (hhi : i < base+n) :
    f i = true := by
  induction n generalizing base with
  | zero => omega
  | succ n ih =>
    simp only [scanRange,Bool.and_eq_true] at h
    by_cases e : i = base
    · simpa [e] using h.1
    · apply ih (base+1) h.2 <;> omega

/-- Exhaustive native evaluation of a closed, executable Lean checker.
The compiler/runtime trust of native_decide is reported in the axiom audit. -/
theorem all_profile_masks_checked : scanRange checkProfileMask 0 8388608 = true := by
  native_decide

theorem profile_mask_complete (m : Nat) (hm : m < 8388608)
    (hc : countBits m 23 = 11)
    (h1 : (coefficientState m 23).first = 0)
    (h3 : (coefficientState m 23).third = 0) :
    m ∈ coefficientProfiles[(coefficientState m 23).second.val]! := by
  have h := scanRange_sound checkProfileMask 0 8388608 all_profile_masks_checked m (by omega) hm
  simpa [checkProfileMask,hc,h1,h3] using h

#print axioms all_profile_masks_checked
#print axioms profile_mask_complete

end ToroidalQueens23
