import Erdos335.CompactSigmaRepresentatives
import Erdos335.CompactDysonSigma

/-!
# Sigma-compact representatives in a quotient

For a measurable saturated set, compact approximation gives a Borel
quotient representative with the same pullback up to measure zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem exists_sigmaCompact_quotient_representative
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    [TopologicalSpace G] [TopologicalSpace K] [T2Space G] [T2Space K]
    [MeasurableSpace G] [MeasurableSpace K] [BorelSpace G] [BorelSpace K]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (φ : G →+ K) (hφ : Continuous φ) (S : Set G) (hS : MeasurableSet S)
    (hperiod : ∀ h ∈ φ.ker, h +ᵥ S = S) :
    ∃ T : Set K, IsSigmaCompact T ∧ MeasurableSet T ∧ φ ⁻¹' T =ᵐ[μ] S := by
  obtain ⟨C, hCS, hCsc, _, hCmass⟩ := exists_full_measure_sigmaCompact_subset μ S hS
  let T := φ '' C
  have hTsc : IsSigmaCompact T := hCsc.image hφ
  have hTm : MeasurableSet T := measurableSet_of_sigmaCompact T hTsc
  have hpre : MeasurableSet (φ ⁻¹' T) := hTm.preimage hφ.measurable
  have hCpre : C ⊆ φ ⁻¹' T := subset_preimage_image _ _
  have hsub : φ ⁻¹' T ⊆ S := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := hx
    have hker : x - c ∈ φ.ker := by
      change φ (x - c) = 0
      rw [map_sub, hcx, sub_self]
    have hmem : x ∈ (x - c) +ᵥ S := ⟨c, hCS hc, by simp [vadd_eq_add]⟩
    rwa [hperiod (x - c) hker] at hmem
  refine ⟨T, hTsc, hTm, ?_⟩
  apply ae_eq_of_subset_of_measure_ge hsub _ hpre.nullMeasurableSet (measure_ne_top μ S)
  rw [← hCmass]
  exact measure_mono hCpre

end Erdos335.Loeb

end
