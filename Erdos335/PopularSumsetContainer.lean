import Erdos335.PopularSumsetRemoval

/-!
# Literal sumset containers from popular sumset estimates
-/

set_option autoImplicit false

open Finset
open scoped Pointwise

noncomputable section

namespace Erdos335.ArithmeticRemoval

theorem popular_sumset_container
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B C : Finset G) (τ η : ℝ) (hτ : 0 < τ)
    (hpopular : ((popularSum A B (popularRemovalBound τ) \ C).card : ℝ) ≤ η * Fintype.card G) :
    ∃ A' ⊆ A, ∃ B' ⊆ B,
      ((A \ A').card : ℝ) < τ * Fintype.card G ∧
      ((B \ B').card : ℝ) < τ * Fintype.card G ∧
      (((A' + B') \ C).card : ℝ) < (τ + η) * Fintype.card G := by
  classical
  obtain ⟨A', hA', B', hB', hAcut, hBcut, hsum⟩ := popular_sumset_removal A B τ hτ
  refine ⟨A', hA', B', hB', hAcut, hBcut, ?_⟩
  let P := popularSum A B (popularRemovalBound τ)
  have hsub : (A' + B') \ C ⊆ ((A' + B') \ P) ∪ (P \ C) := by
    intro x hx
    obtain ⟨hxAB, hxC⟩ := mem_sdiff.mp hx
    by_cases hxP : x ∈ P
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hxP, hxC⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hxAB, hxP⟩)
  have hcard : (((A' + B') \ C).card : ℝ) ≤
      (((A' + B') \ P).card : ℝ) + (P \ C).card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  change (((A' + B') \ P).card : ℝ) < τ * Fintype.card G at hsum
  change ((P \ C).card : ℝ) ≤ η * Fintype.card G at hpopular
  nlinarith

end Erdos335.ArithmeticRemoval

end
