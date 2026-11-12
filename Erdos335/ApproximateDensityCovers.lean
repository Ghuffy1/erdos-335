import Erdos335.DensityAlgebra

/-!
# Ordinary density equivalence from common approximate covers
-/

set_option autoImplicit false

open Filter Topology Set

namespace Erdos335

theorem densityEquivalent_of_common_approximate_covers
    (A B : Set ℕ) (d : ℝ) (hA : HasDensity A d) (hB : HasDensity B d)
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ (C : Set ℕ) (c : ℝ),
      A ⊆ C ∧ B ⊆ C ∧ HasDensity C c ∧ c ≤ d + ε) :
    DensityEquivalent A B := by
  have hAB : Negligible (A \ B) := by
    apply tendsto_order.mpr
    constructor
    · intro x hx
      exact Eventually.of_forall fun n => lt_of_lt_of_le hx (by positivity)
    · intro ε hε
      obtain ⟨C, c, hAC, hBC, hC, hc⟩ := hcover (ε / 2) (by linarith)
      have hBCzero : Negligible (B \ C) := by
        rw [show B \ C = ∅ from Set.diff_eq_empty.mpr hBC]
        exact hasDensity_empty
      have hCB := hC.sdiff_of_negligible_reverse hB hBCzero
      have hsmall : c - d < ε := by linarith
      have hevent := hCB.eventually (gt_mem_nhds hsmall)
      filter_upwards [hevent] with n hn
      exact lt_of_le_of_lt (div_le_div_of_nonneg_right
        (by exact_mod_cast count_mono (Set.diff_subset_diff_left hAC) n)
        (Nat.cast_nonneg n)) hn
  refine ⟨hAB, ?_⟩
  change HasDensity (B \ A) 0
  simpa only [sub_self] using hB.sdiff_of_negligible_reverse hA hAB

end Erdos335
