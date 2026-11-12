import Erdos335.CompactQuotientPairCores
import Erdos335.LoebCompactInputPeriods
import Erdos335.CompactQuotientAperiodicity

/-!
# A compatible aperiodic quotient model for an irreducible Loeb pair
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance compactQuotientPairLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_compact_aperiodic_quotient_pair
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K L : Type*} [AddCommGroup K] [AddCommGroup L]
    [TopologicalSpace K] [TopologicalSpace L] [IsTopologicalAddGroup K]
    [IsTopologicalAddGroup L] [CompactSpace K] [T2Space K] [T2Space L] [PolishSpace K]
    [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
    [MeasurableAdd₂ K] [MeasurableNeg K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (ψ : K →+ L) (hψ : Continuous ψ) (hψsurj : Function.Surjective ψ)
    (C D : Set K) (hCm : MeasurableSet C) (hDm : MeasurableSet D)
    (hCDm : MeasurableSet (C + D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hker : ∀ t : K, t ∈ ψ.ker ↔
      t +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D) :
    ∃ P Q : Set L, IsSigmaCompact P ∧ IsSigmaCompact Q ∧
      MeasurableSet P ∧ MeasurableSet Q ∧ MeasurableSet (P + Q) ∧
      (ψ.comp φ) ⁻¹' P =ᵐ[loebMeasure U hU] φ ⁻¹' C ∧
      (ψ.comp φ) ⁻¹' Q =ᵐ[loebMeasure U hU] φ ⁻¹' D ∧
      (ψ.comp φ) ⁻¹' (P + Q) =ᵐ[loebMeasure U hU] φ ⁻¹' (C + D) ∧
      ∀ t : L, t +ᵥ (P + Q) =ᵐ[Measure.map (ψ.comp φ) (loebMeasure U hU)] P + Q → t = 0 := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure ν := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have : ν.IsNegInvariant := loebMeasure_map_hom_isNegInvariant U hU q φ hφ
  have hperiod (t : K) (ht : t ∈ ψ.ker) :
      (t +ᵥ C =ᵐ[ν] C) ∧ (t +ᵥ D =ᵐ[ν] D) :=
    compact_factor_nonextendible_inputs_ae_period U hU q φ hφ hsurj C D hCm hDm hne t
      ((hker t).mp ht)
  obtain ⟨A, B, hAsc, hBsc, hAm, hBm, hAC, hBD, hAmass, hBmass,
      hAmodel, hBmodel, hsumExact⟩ := exists_quotient_pair_cores ν ψ hψ C D hCm hDm
        (fun t ht => (hperiod t ht).1) (fun t ht => (hperiod t ht).2)
  let P := ψ '' A
  let Q := ψ '' B
  have hPsc : IsSigmaCompact P := hAsc.image hψ
  have hQsc : IsSigmaCompact Q := hBsc.image hψ
  have hPm : MeasurableSet P := measurableSet_of_sigmaCompact P hPsc
  have hQm : MeasurableSet Q := measurableSet_of_sigmaCompact Q hQsc
  have hPQm : MeasurableSet (P + Q) :=
    measurableSet_of_sigmaCompact _ (isSigmaCompact_add_sets P Q hPsc hQsc)
  have hABm : MeasurableSet (A + B) :=
    measurableSet_of_sigmaCompact _ (isSigmaCompact_add_sets A B hAsc hBsc)
  have hAmass' : μ (φ ⁻¹' A) = μ (φ ⁻¹' C) := by
    rw [← Measure.map_apply hφ hAm, ← Measure.map_apply hφ hCm]
    exact hAmass
  have hBmass' : μ (φ ⁻¹' B) = μ (φ ⁻¹' D) := by
    rw [← Measure.map_apply hφ hBm, ← Measure.map_apply hφ hDm]
    exact hBmass
  have hcoreInner := hirr (φ ⁻¹' A) (φ ⁻¹' B) (hAm.preimage hφ) (hBm.preimage hφ)
    (preimage_mono hAC) (preimage_mono hBD) hAmass' hBmass'
  rw [← preimage_add_of_surjective_addHom φ hsurj A B,
    ← preimage_add_of_surjective_addHom φ hsurj C D,
    internalInnerMeasure_eq U hU _ (hABm.preimage hφ),
    internalInnerMeasure_eq U hU _ (hCDm.preimage hφ)] at hcoreInner
  have hcoreAe : φ ⁻¹' (A + B) =ᵐ[μ] φ ⁻¹' (C + D) :=
    ae_eq_of_subset_of_measure_ge (preimage_mono (add_subset_add hAC hBD)) hcoreInner.ge
      (hABm.preimage hφ).nullMeasurableSet (measure_ne_top μ _)
  have hcompactAe : A + B =ᵐ[ν] C + D :=
    ae_map_set_eq_of_preimage μ φ hφ (A + B) (C + D) hABm hCDm hcoreAe
  have hquotientModel : ψ ⁻¹' (P + Q) =ᵐ[ν] C + D := by
    rw [hsumExact]
    exact hcompactAe
  have hker' : ψ.ker = AddAction.aestabilizer K ν (C + D) := by
    ext t
    exact hker t
  have haperiodic := quotient_representative_has_trivial_ae_stabilizer ν ψ hψ.measurable
    hψsurj (C + D) (P + Q) hquotientModel hker'
  refine ⟨P, Q, hPsc, hQsc, hPm, hQm, hPQm, ?_, ?_, ?_, ?_⟩
  · exact ae_of_ae_map hφ.aemeasurable hAmodel
  · exact ae_of_ae_map hφ.aemeasurable hBmodel
  · change φ ⁻¹' (ψ ⁻¹' (P + Q)) =ᵐ[μ] φ ⁻¹' (C + D)
    rw [hsumExact]
    exact hcoreAe
  · simpa only [ν, μ, Measure.map_map hψ.measurable hφ, AddMonoidHom.coe_comp] using haperiodic

end Erdos335.Loeb

end
