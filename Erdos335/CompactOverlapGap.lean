import Erdos335.CompactOverlapSubadditive

/-!
# A uniform overlap gap away from the identity
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Topology Pointwise

namespace Erdos335.Loeb

theorem exists_positive_haarOverlap_loss_on_compact
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (S : Set G) (hS : MeasurableSet S)
    (hperiod : ∀ t : G, t +ᵥ S =ᵐ[μ] S → t = 0)
    (E : Set G) (hE : IsCompact E) (hzero : 0 ∉ E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ E, ε ≤ (μ S).toReal - haarOverlap μ S t := by
  by_cases hnonempty : E.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hE.exists_isMaxOn hnonempty
      (continuous_haarOverlap μ S hS).continuousOn
    have hz0 : z ≠ 0 := fun heq => hzero (heq ▸ hz)
    have hstrict := haarOverlap_strict_maximum μ S hS hperiod z hz0
    have hstrict' : haarOverlap μ S z < (μ S).toReal := by
      simpa only [haarOverlap, zero_vadd, inter_self] using hstrict
    refine ⟨(μ S).toReal - haarOverlap μ S z, sub_pos.mpr hstrict', ?_⟩
    intro t ht
    exact sub_le_sub_left (hmax ht) _
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    exact (hnonempty ⟨t, ht⟩).elim

theorem exists_uniform_scaled_difference_mass_lower_bound
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (S : Set G) (hS : MeasurableSet S)
    (hperiod : ∀ t : G, t +ᵥ S =ᵐ[μ] S → t = 0)
    (E : Set G) (hE : IsCompact E) (hzero : 0 ∉ E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ A B : Set G, (A + B ≤ᵐ[μ] S) →
      ∀ x ∈ B, ∀ y ∈ B, ∀ n : ℕ, n • (x - y) ∈ E →
        ε ≤ n * ((μ S).toReal - (μ A).toReal) := by
  obtain ⟨ε, hε, hbound⟩ := exists_positive_haarOverlap_loss_on_compact μ S hS hperiod E hE hzero
  refine ⟨ε, hε, ?_⟩
  intro A B hsum x hx y hy n hn
  exact (hbound _ hn).trans (haarOverlap_nsmul_loss_le_of_sumset μ A B S hS hsum x y hx hy n)

end Erdos335.Loeb
