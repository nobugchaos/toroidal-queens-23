import ToroidalQueens23

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace SemanticAudit

abbrev Cell := ZMod 23 × ZMod 23

/-- Pairwise distinct row, column and both wrapped diagonal labels. -/
def physicalIndependent (s : Finset Cell) : Prop :=
  ∀ q ∈ s, ∀ z ∈ s, q ≠ z →
    q.1 ≠ z.1 ∧ q.2 ≠ z.2 ∧ q.1 + q.2 ≠ z.1 + z.2 ∧ q.1 - q.2 ≠ z.1 - z.2

/-- Every cell is occupied, or attacked by a different queen. -/
def physicalDominating (s : Finset Cell) : Prop :=
  ∀ z, z ∈ s ∨ ∃ q ∈ s, q ≠ z ∧
    (q.1 = z.1 ∨ q.2 = z.2 ∨ q.1 + q.2 = z.1 + z.2 ∨ q.1 - q.2 = z.1 - z.2)

theorem independence_matches (s : Finset Cell) :
    ToroidalQueens23.Independent s ↔ physicalIndependent s := by
  simp only [ToroidalQueens23.Independent, physicalIndependent,
    ToroidalQueens23.Covers, not_or]

theorem domination_matches (s : Finset Cell) :
    ToroidalQueens23.Dominating s ↔ physicalDominating s := by
  constructor
  · intro h z
    by_cases hz : z ∈ s
    · exact Or.inl hz
    · obtain ⟨q,hq,hcover⟩ := h z
      exact Or.inr ⟨q,hq,(fun he => hz (he ▸ hq)),hcover⟩
  · intro h z
    rcases h z with hz | ⟨q,hq,hne,hcover⟩
    · exact ⟨z,hz,Or.inl rfl⟩
    · exact ⟨q,hq,hcover⟩

theorem physically_stated_exact_minimum :
    (∃ s : Finset Cell, s.card = 12 ∧ physicalIndependent s ∧ physicalDominating s) ∧
    (∀ s : Finset Cell, physicalIndependent s → physicalDominating s → 12 ≤ s.card) := by
  constructor
  · obtain ⟨s,hc,hi,hd⟩ := ToroidalQueens23.twelve_suffice
    exact ⟨s,hc,(independence_matches s).mp hi,(domination_matches s).mp hd⟩
  · intro s hi hd
    exact ToroidalQueens23.independent_dominating_card_at_least_twelve s
      ((independence_matches s).mpr hi) ((domination_matches s).mpr hd)

example : Fintype.card Cell = 529 := by simp [Cell]
example : ToroidalQueens23.Covers (22,0) (0,1) := by
  unfold ToroidalQueens23.Covers
  decide
example : ToroidalQueens23.Covers (22,22) (0,21) := by
  unfold ToroidalQueens23.Covers
  decide
example : ¬ ToroidalQueens23.Covers (0,0) (1,2) := by
  unfold ToroidalQueens23.Covers
  decide
example : ¬ ToroidalQueens23.Dominating ∅ := by
  simp [ToroidalQueens23.Dominating]
example : ¬ ToroidalQueens23.Independent {(22,0), (0,1)} := by
  intro h
  apply h (22,0) (by simp) (0,1) (by simp) (by decide)
  unfold ToroidalQueens23.Covers
  decide

#check physically_stated_exact_minimum
#print axioms independence_matches
#print axioms domination_matches
#print axioms physically_stated_exact_minimum

end SemanticAudit
