import ToroidalQueens23.LowerTen
import ToroidalQueens23.CoverSemantics
import ToroidalQueens23.ProfileBridge
import ToroidalQueens23.Upper
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option maxHeartbeats 4000000

namespace ToroidalQueens23
noncomputable section

theorem needed_differences_subset (s : Finset Square) (h : Dominating s) :
    neededDifferences (rowSet s) (colSet s) (sumSet s) ⊆ diffSet s := by
  intro d hd
  obtain ⟨r,hr,hc,hs⟩ := (Finset.mem_filter.mp hd).2
  obtain ⟨q,hq,hcover⟩ := h (r,r-d)
  rcases hcover with hR | hC | hS | hD
  · exact False.elim (hr (Finset.mem_image.mpr ⟨q,hq,hR⟩))
  · exact False.elim (hc (Finset.mem_image.mpr ⟨q,hq,hC⟩))
  · apply False.elim
    apply hs
    apply Finset.mem_image.mpr
    refine ⟨q,hq,?_⟩
    calc q.1+q.2 = r+(r-d) := hS
         _ = 2*r-d := by ring
  · apply Finset.mem_image.mpr
    refine ⟨q,hq,?_⟩
    calc q.1-q.2 = r-(r-d) := hD
         _ = d := by ring

theorem eleven_impossible (s : Finset Square) (hi : Independent s) (hd : Dominating s) :
    s.card ≠ 11 := by
  intro hc
  let t := centered s
  have htI : Independent t := centered_independent s hi
  have htD : Dominating t := centered_dominating s hd
  have htC : t.card = 11 := by simpa [t,centered_card] using hc
  have hcards := projection_cards t htI
  rw [htC] at hcards
  have hsums := projection_sums t htI (centered_sum_row s hc) (centered_sum_col s hc)
  obtain ⟨hRC,hSD,hvR,hvC,hvS,_⟩ := cover_constraints
    (rowSet t) (colSet t) (sumSet t) (diffSet t) hcards hsums (coverPolynomial_vanishes t htD)
  have hdouble := quadratic_doubling t htI hsums hRC hSD
  have hpR := root_profile_complete (rowSet t) hcards.1 hsums.1 hvR
  have hpC := root_profile_complete (colSet t) hcards.2.1 hsums.2.1 hvC
  have hpS := root_profile_complete (sumSet t) hcards.2.2.1 hsums.2.2.1 hvS
  change (encodeMask (rowSet t)).toNat ∈ coefficientProfiles[(rootU (rowSet t)).val]! at hpR
  change (encodeMask (colSet t)).toNat ∈ coefficientProfiles[(rootU (colSet t)).val]! at hpC
  change (encodeMask (sumSet t)).toNat ∈ coefficientProfiles[(rootU (sumSet t)).val]! at hpS
  rw [← hRC] at hpC
  rw [hdouble] at hpS
  have hlo := profile_cover_lower_bound (rootU (rowSet t)) (rowSet t) (colSet t) (sumSet t) hpR hpC hpS
  have hhi := Finset.card_le_card (needed_differences_subset t htD)
  rw [hcards.2.2.2] at hhi
  omega

theorem independent_dominating_card_at_least_twelve (s : Finset Square)
    (hi : Independent s) (hd : Dominating s) : 12 ≤ s.card := by
  have hlo := dominating_card_at_least_eleven s hd
  have hne := eleven_impossible s hi hd
  omega

/-- A quantifier-complete exact minimum statement for the 23 by 23 torus. -/
theorem minimum_is_twelve :
    (∃ s : Finset Square, s.card = 12 ∧ Independent s ∧ Dominating s) ∧
    (∀ s : Finset Square, Independent s → Dominating s → 12 ≤ s.card) :=
  ⟨twelve_suffice,independent_dominating_card_at_least_twelve⟩

noncomputable def independentDominationNumber : Nat :=
  sInf {k : Nat | ∃ s : Finset Square, s.card = k ∧ Independent s ∧ Dominating s}

theorem independentDominationNumber_eq_twelve : independentDominationNumber = 12 := by
  apply le_antisymm
  · exact Nat.sInf_le twelve_suffice
  · apply le_csInf
    · exact ⟨12,twelve_suffice⟩
    · rintro k ⟨s,hc,hi,hd⟩
      rw [← hc]
      exact independent_dominating_card_at_least_twelve s hi hd

#print axioms dominating_card_at_least_eleven
#print axioms eleven_impossible
#print axioms minimum_is_twelve
#print axioms independentDominationNumber_eq_twelve

end
end ToroidalQueens23
