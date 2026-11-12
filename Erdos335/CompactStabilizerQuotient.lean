import Erdos335.CompactInvariantRepresentative
import Erdos335.CompactHaarProbability
import Erdos335.CompactQuotientRepresentative
import Erdos335.CompactQuotientAperiodicity

/-!
# A measurable model after quotienting by the essential stabilizer
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem exists_aperiodic_quotient_representative
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    [TopologicalSpace G] [TopologicalSpace K] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [T2Space K]
    [MeasurableSpace G] [MeasurableSpace K] [BorelSpace G] [BorelSpace K]
    [MeasurableAdd₂ G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsAddLeftInvariant]
    (φ : G →+ K) (hφ : Continuous φ) (hsurj : Function.Surjective φ)
    (S : Set G) (hS : MeasurableSet S)
    (hker : φ.ker = AddAction.aestabilizer G μ S) :
    ∃ T : Set K, IsSigmaCompact T ∧ MeasurableSet T ∧ φ ⁻¹' T =ᵐ[μ] S ∧
      ∀ t : K, t +ᵥ T =ᵐ[Measure.map φ μ] T → t = 0 := by
  have hclosed : IsClosed (φ.ker : Set G) := by
    change IsClosed (φ ⁻¹' ({0} : Set K))
    exact isClosed_singleton.preimage hφ
  have : CompactSpace φ.ker := isCompact_iff_compactSpace.mp hclosed.isCompact
  have : MeasurableAdd₂ φ.ker := ⟨by
    exact ((measurable_subtype_coe.comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk⟩
  obtain ⟨ν, hνprob, hνhaar⟩ := exists_compact_addHaar_probability φ.ker
  have : IsProbabilityMeasure ν := hνprob
  have : Measure.IsAddHaarMeasure ν := hνhaar
  have hperiod (h : φ.ker) : (h : G) +ᵥ S =ᵐ[μ] S := by
    exact hker.le h.property
  obtain ⟨S₀, hS₀m, hS₀ae, hS₀period⟩ := exists_exact_invariant_ae_set μ ν φ.ker.subtype
    continuous_subtype_val.measurable S hS hperiod
  obtain ⟨T, hTsc, hTm, hTae⟩ := exists_sigmaCompact_quotient_representative μ φ hφ S₀ hS₀m
    (fun h hh => hS₀period ⟨h, hh⟩)
  have hmodel : φ ⁻¹' T =ᵐ[μ] S := hTae.trans hS₀ae
  exact ⟨T, hTsc, hTm, hmodel,
    quotient_representative_has_trivial_ae_stabilizer μ φ hφ.measurable hsurj S T hmodel hker⟩

end Erdos335.Loeb

end
