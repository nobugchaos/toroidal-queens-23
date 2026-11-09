import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

namespace ToroidalQueens23

abbrev F := ZMod 23
abbrev Square := F × F

instance : Fact (Nat.Prime 23) := ⟨by decide⟩
instance : Nontrivial F := by infer_instance

def Covers (q z : Square) : Prop :=
  q.1 = z.1 ∨ q.2 = z.2 ∨ q.1 + q.2 = z.1 + z.2 ∨ q.1 - q.2 = z.1 - z.2

def Independent (s : Finset Square) : Prop :=
  ∀ q ∈ s, ∀ z ∈ s, q ≠ z → ¬ Covers q z

def Dominating (s : Finset Square) : Prop :=
  ∀ z, ∃ q ∈ s, Covers q z

def translate (a b : F) (q : Square) : Square := (q.1+a,q.2+b)

theorem translate_injective (a b : F) : Function.Injective (translate a b) := by
  intro q z h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (add_right_cancel h1) (add_right_cancel h2)

theorem covers_translate_iff (a b : F) (q z : Square) :
    Covers (translate a b q) (translate a b z) ↔ Covers q z := by
  have hs (u v : F) : (u+a)+(v+b) = (u+v)+(a+b) := by ring
  have hd (u v : F) : (u+a)-(v+b) = (u-v)+(a-b) := by ring
  simp only [Covers,translate,hs,hd,add_left_inj]

theorem independent_translate (s : Finset Square) (h : Independent s) (a b : F) :
    Independent (s.image (translate a b)) := by
  intro q hq z hz hne hc
  obtain ⟨q,hq0,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨z,hz0,rfl⟩ := Finset.mem_image.mp hz
  apply h q hq0 z hz0
  · intro e
    exact hne (congrArg (translate a b) e)
  · exact (covers_translate_iff a b q z).mp hc

theorem dominating_translate (s : Finset Square) (h : Dominating s) (a b : F) :
    Dominating (s.image (translate a b)) := by
  intro z
  obtain ⟨q,hq,hc⟩ := h (translate (-a) (-b) z)
  refine ⟨translate a b q,Finset.mem_image.mpr ⟨q,hq,rfl⟩,?_⟩
  have ht : translate a b (translate (-a) (-b) z) = z := by
    apply Prod.ext <;> simp [translate,add_assoc]
  rw [← ht]
  exact (covers_translate_iff a b q _).mpr hc

theorem cardinal_translate (s : Finset Square) (a b : F) :
    (s.image (translate a b)).card = s.card :=
  Finset.card_image_of_injective _ (translate_injective a b)

def rowMean (s : Finset Square) : F := 21 * ∑ q ∈ s, q.1
def colMean (s : Finset Square) : F := 21 * ∑ q ∈ s, q.2
def centered (s : Finset Square) : Finset Square :=
  s.image (translate (-rowMean s) (-colMean s))

theorem centered_card (s : Finset Square) : (centered s).card = s.card :=
  cardinal_translate s _ _

theorem centered_independent (s : Finset Square) (h : Independent s) :
    Independent (centered s) := independent_translate s h _ _

theorem centered_dominating (s : Finset Square) (h : Dominating s) :
    Dominating (centered s) := dominating_translate s h _ _

theorem centered_sum_row (s : Finset Square) (hcard : s.card = 11) :
    ∑ q ∈ centered s, q.1 = 0 := by
  classical
  unfold centered
  rw [Finset.sum_image (translate_injective _ _).injOn]
  simp only [translate]
  rw [Finset.sum_add_distrib,Finset.sum_const,hcard,nsmul_eq_mul]
  unfold rowMean
  have hinv : (11 : F)*21 = 1 := by decide
  calc
    (∑ q ∈ s, q.1) + 11*(-(21*(∑ q ∈ s, q.1))) =
      (1-11*21)*(∑ q ∈ s, q.1) := by ring
    _ = 0 := by rw [hinv]; simp

theorem centered_sum_col (s : Finset Square) (hcard : s.card = 11) :
    ∑ q ∈ centered s, q.2 = 0 := by
  classical
  unfold centered
  rw [Finset.sum_image (translate_injective _ _).injOn]
  simp only [translate]
  rw [Finset.sum_add_distrib,Finset.sum_const,hcard,nsmul_eq_mul]
  unfold colMean
  have hinv : (11 : F)*21 = 1 := by decide
  calc
    (∑ q ∈ s, q.2) + 11*(-(21*(∑ q ∈ s, q.2))) =
      (1-11*21)*(∑ q ∈ s, q.2) := by ring
    _ = 0 := by rw [hinv]; simp

theorem row_inj_on {s : Finset Square} (h : Independent s) :
    Set.InjOn Prod.fst (s : Set Square) := by
  intro q hq z hz e
  by_contra hne
  exact h q hq z hz hne (Or.inl e)

theorem col_inj_on {s : Finset Square} (h : Independent s) :
    Set.InjOn Prod.snd (s : Set Square) := by
  intro q hq z hz e
  by_contra hne
  exact h q hq z hz hne (Or.inr (Or.inl e))

theorem sum_inj_on {s : Finset Square} (h : Independent s) :
    Set.InjOn (fun q => q.1+q.2) (s : Set Square) := by
  intro q hq z hz e
  by_contra hne
  exact h q hq z hz hne (Or.inr (Or.inr (Or.inl e)))

theorem diff_inj_on {s : Finset Square} (h : Independent s) :
    Set.InjOn (fun q => q.1-q.2) (s : Set Square) := by
  intro q hq z hz e
  by_contra hne
  exact h q hq z hz hne (Or.inr (Or.inr (Or.inr e)))

end ToroidalQueens23
