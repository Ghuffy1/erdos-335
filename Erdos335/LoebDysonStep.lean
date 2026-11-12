import Erdos335.CompactDysonPullback
import Erdos335.LoebCompactShrinkingStep
import Erdos335.LoebGeneralStrictDysonPair

/-!
# A shrinking Dyson step or a quasi-periodic input pair

The compact overlap estimate supplies a positive smaller right input.
Strict loss of sumset measure gives the input-pair theorem. Otherwise
the transformed sumset is measurable and agrees almost everywhere
with the original sumset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance dysonStepLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_compact_dyson_step_or_quasiPeriodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [PolishSpace K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableAdd₂ K] [MeasurableNeg K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set K) (hCm : MeasurableSet C) (hDm : MeasurableSet D)
    (hCDm : MeasurableSet (C + D))
    (hCpos : 0 < Measure.map φ (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map φ (loebMeasure U hU) D)
    (hcomp : 0 < loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D))ᶜ)
    (hfull : loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D)) =
      loebMeasure U hU (φ ⁻¹' C) + loebMeasure U hU (φ ⁻¹' D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ ((φ ⁻¹' C) + (φ ⁻¹' D)) =ᵐ[loebMeasure U hU]
        (φ ⁻¹' C) + (φ ⁻¹' D)) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨
    ∃ e : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)),
      let L := dysonGroupLeft (φ ⁻¹' C) (φ ⁻¹' D) e
      let R := dysonGroupRight (φ ⁻¹' C) (φ ⁻¹' D) e
      0 < loebMeasure U hU R ∧
      (loebMeasure U hU R).toReal ≤
        (1 - (loebMeasure U hU (φ ⁻¹' D)).toReal) *
          (loebMeasure U hU (φ ⁻¹' D)).toReal ∧
      MeasurableSet L ∧ MeasurableSet R ∧ MeasurableSet (L + R) ∧
      L + R =ᵐ[loebMeasure U hU] (φ ⁻¹' C) + (φ ⁻¹' D) ∧
      loebMeasure U hU (L + R) = loebMeasure U hU L + loebMeasure U hU R ∧
      loebMeasure U hU L + loebMeasure U hU R =
        loebMeasure U hU (φ ⁻¹' C) + loebMeasure U hU (φ ⁻¹' D) := by
  classical
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  let A := φ ⁻¹' C
  let B := φ ⁻¹' D
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure ν := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have hAm : MeasurableSet A := hCm.preimage hφ
  have hBm : MeasurableSet B := hDm.preimage hφ
  have hSm : MeasurableSet (A + B) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D]
    exact hCDm.preimage hφ
  have hAmass : μ A = ν C := (Measure.map_apply hφ hCm).symm
  have hBmass : μ B = ν D := (Measure.map_apply hφ hDm).symm
  have htotal : (ν C).toReal + (ν D).toReal ≤ 1 := by
    rw [← hAmass, ← hBmass,
      ← ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ B), ← hfull]
    have hle : μ (A + B) ≤ 1 := by
      simpa using (measure_mono (subset_univ (A + B)) : μ (A + B) ≤ μ univ)
    simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle
  obtain ⟨k, hkpos, hkbound⟩ := exists_shrinking_parameter_in_irreducible_compact_factor
    U hU q φ hφ hsurj C D hCm hDm hCDm hCpos hDpos htotal hirr hnoAE
  obtain ⟨e, he⟩ := hsurj k
  let L := dysonGroupLeft A B e
  let R := dysonGroupRight A B e
  obtain ⟨hLmK, hRmK⟩ := measurableSet_dysonGroup C D hCm hDm (φ e)
  have hLm : MeasurableSet L := by
    change MeasurableSet (dysonGroupLeft (φ ⁻¹' C) (φ ⁻¹' D) e)
    rw [← preimage_dysonGroupLeft φ C D e]
    exact hLmK.preimage hφ
  have hRm : MeasurableSet R := by
    change MeasurableSet (dysonGroupRight (φ ⁻¹' C) (φ ⁻¹' D) e)
    rw [← preimage_dysonGroupRight φ C D e]
    exact hRmK.preimage hφ
  have hLmass : μ L = ν (dysonGroupLeft C D (φ e)) := by
    change μ (dysonGroupLeft (φ ⁻¹' C) (φ ⁻¹' D) e) = _
    rw [← preimage_dysonGroupLeft φ C D e]
    exact (Measure.map_apply hφ hLmK).symm
  have hRmass : μ R = ν (dysonGroupRight C D k) := by
    change μ (dysonGroupRight (φ ⁻¹' C) (φ ⁻¹' D) e) = _
    rw [← he, ← preimage_dysonGroupRight φ C D e]
    exact (Measure.map_apply hφ hRmK).symm
  have hRpos : 0 < μ R := by
    rw [hRmass]
    exact (ENNReal.toReal_pos_iff.mp hkpos).1
  have hRbound : (μ R).toReal ≤ (1 - (μ B).toReal) * (μ B).toReal := by
    rw [hRmass, hBmass]
    exact hkbound
  have hmass : μ L + μ R = μ A + μ B := by
    rw [hLmass, hRmass, ← he, hAmass, hBmass]
    exact dysonGroup_measure_identity ν C D hDm (φ e)
  by_cases hsmall : internalInnerMeasure U hU (L + R) < μ A + μ B
  · exact Or.inl (loeb_general_strict_dyson_quasiPeriodic_pair U hU q A B hAm hBm hSm e
      hRpos hcomp hfull hsmall hirr hne hnoAE)
  · right
    have hsubset : L + R ⊆ A + B := dysonGroup_sum_subset A B e
    have hinner : internalInnerMeasure U hU (L + R) = μ (A + B) := by
      apply le_antisymm
      · exact (internalInnerMeasure_mono U hU hsubset).trans_eq
          (internalInnerMeasure_eq U hU _ hSm)
      · rw [hfull]
        exact le_of_not_gt hsmall
    obtain ⟨hLRm, hLRae⟩ := measurable_of_subset_full_inner U hU (L + R) (A + B)
      hsubset hSm hinner
    refine ⟨e, hRpos, hRbound, hLm, hRm, hLRm, hLRae, ?_, hmass⟩
    rw [measure_congr hLRae, hfull, hmass]

end Erdos335.Loeb

end
