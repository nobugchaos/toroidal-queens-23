import ToroidalQueens23.Basic

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace ToroidalQueens23

def witness : Finset Square :=
  {(2,13), (3,9), (6,3), (7,22), (9,2), (11,5),
   (12,8), (15,18), (16,14), (18,7), (20,4), (21,0)}

theorem witness_card : witness.card = 12 := by decide

theorem witness_independent : Independent witness := by
  unfold Independent Covers witness
  decide

theorem witness_dominating : Dominating witness := by
  unfold Dominating Covers witness
  decide

theorem twelve_suffice : ∃ s : Finset Square,
    s.card = 12 ∧ Independent s ∧ Dominating s :=
  ⟨witness,witness_card,witness_independent,witness_dominating⟩

#print axioms twelve_suffice

end ToroidalQueens23
