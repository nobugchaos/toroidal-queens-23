import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

namespace ToroidalQueens23

abbrev Square := Fin 23 × Fin 23

/-- Attack or occupation on the torus, including the wraparound diagonals. -/
def Covers (a b : Square) : Prop :=
  a.1 = b.1 ∨ a.2 = b.2 ∨
  (a.1.val + a.2.val) % 23 = (b.1.val + b.2.val) % 23 ∨
  (a.1.val + 23 - a.2.val) % 23 = (b.1.val + 23 - b.2.val) % 23

instance (a b : Square) : Decidable (Covers a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def witness : Finset Square :=
  {(2,13), (3,9), (6,3), (7,22), (9,2), (11,5),
   (12,8), (15,18), (16,14), (18,7), (20,4), (21,0)}

def Independent (s : Finset Square) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ Covers a b

def Dominating (s : Finset Square) : Prop :=
  ∀ b : Square, ∃ a ∈ s, Covers a b

theorem witness_card : witness.card = 12 := by decide

theorem witness_independent : Independent witness := by
  unfold Independent
  decide

theorem witness_dominating : Dominating witness := by
  unfold Dominating
  decide

theorem twelve_suffice : ∃ s : Finset Square,
    s.card = 12 ∧ Independent s ∧ Dominating s :=
  ⟨witness, witness_card, witness_independent, witness_dominating⟩

#print axioms witness_card
#print axioms witness_independent
#print axioms witness_dominating
#print axioms twelve_suffice

end ToroidalQueens23
