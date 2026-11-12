import Erdos335.CompactProfileAverage
import Erdos335.LoebQuotientDifference
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A shrinking Dyson step in a nonperiodic compact quotient

Positive-intersection regularization identifies the difference set with
the positive support of the overlap profile. The Loeb difference theorem
then provides its measure bound and the first moment method selects a step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem compactIntersectionProfile_eq_dysonMeasure
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] (A B : Set G) (e : G) :
    compactIntersectionProfile μ A B e = (μ (dysonGroupRight A B e)).toReal := by
  unfold compactIntersectionProfile
  rw [← dysonGroup_translate_right, vadd_set_eq_neg_preimage, measure_preimage_add]

local instance compactDysonStepLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_shrinking_step_in_loeb_compact_quotient
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [PolishSpace K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableAdd₂ K] [MeasurableNeg K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set K) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCpos : 0 < Measure.map φ (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map φ (loebMeasure U hU) D)
    (htotal : (Measure.map φ (loebMeasure U hU) C).toReal +
      (Measure.map φ (loebMeasure U hU) D).toReal ≤ 1)
    (hregular : C + (-D) = {e | 0 < compactIntersectionProfile (Measure.map φ (loebMeasure U hU)) C D e})
    (hnotperiod : ¬ ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      ((φ ⁻¹' C) + (φ ⁻¹' D)) + (H : Set _) = (φ ⁻¹' C) + (φ ⁻¹' D)) :
    ∃ e : K, 0 < (Measure.map φ (loebMeasure U hU) (dysonGroupRight C D e)).toReal ∧
      (Measure.map φ (loebMeasure U hU) (dysonGroupRight C D e)).toReal ≤
        (1 - (Measure.map φ (loebMeasure U hU) D).toReal) *
          (Measure.map φ (loebMeasure U hU) D).toReal := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure ν := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have : ν.IsNegInvariant := loebMeasure_map_hom_isNegInvariant U hU q φ hφ
  have hprofile := continuous_compactIntersectionProfile ν C D hC hD
  have hDiff : MeasurableSet (C + (-D)) := by
    rw [hregular]
    exact (isOpen_lt continuous_const hprofile).measurableSet
  have hbound := loeb_quotient_difference_measure_bound U hU q φ hφ hsurj C D hC hD hDiff
    hCpos hDpos hnotperiod
  have hboundR : (ν C).toReal + (ν D).toReal ≤ (ν (C + (-D))).toReal := by
    have h := ENNReal.toReal_mono (measure_ne_top ν _) hbound
    rwa [ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)] at h
  rw [hregular] at hboundR
  obtain ⟨e, hepos, he⟩ := exists_small_positive_intersection ν C D hC hD
    (ENNReal.toReal_pos hCpos.ne' (measure_ne_top ν _))
    (ENNReal.toReal_pos hDpos.ne' (measure_ne_top ν _)) htotal hboundR
  rw [compactIntersectionProfile_eq_dysonMeasure ν C D e] at hepos he
  exact ⟨e, hepos, he⟩

end Erdos335.Loeb

end
