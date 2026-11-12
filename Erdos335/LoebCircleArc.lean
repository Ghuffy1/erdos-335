import Erdos335.LoebCircleMeasurableSumArc
import Erdos335.LoebCircleQuasiPeriodicExclusion

/-!
# The sumset arc conclusion in a surjective circle factor
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance circleArcLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_unitCircle_critical_inputs_measure_lt_one
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ))) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCpos : 0 < volume C) (hDpos : 0 < volume D)
    (hfull : loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D)) =
      loebMeasure U hU (φ ⁻¹' C) + loebMeasure U hU (φ ⁻¹' D)) :
    (volume C).toReal < 1 ∧ (volume D).toReal < 1 := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  have : IsProbabilityMeasure (Measure.map φ μ) := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure (Measure.map φ μ) :=
    loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have hvolume : Measure.map φ μ = volume :=
    Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  have mass (T : Set (AddCircle (1 : ℝ))) (hT : MeasurableSet T) :
      μ (φ ⁻¹' T) = volume T := by
    rw [← Measure.map_apply hφ hT, hvolume]
  have htotal : volume C + volume D ≤ 1 := by
    rw [← mass C hC, ← mass D hD, ← hfull]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ : μ univ = 1)
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top htotal
  rw [ENNReal.toReal_add (measure_ne_top volume _) (measure_ne_top volume _),
    ENNReal.toReal_one] at hreal
  have hCpositive : 0 < (volume C).toReal := ENNReal.toReal_pos hCpos.ne' (measure_ne_top volume _)
  have hDpositive : 0 < (volume D).toReal := ENNReal.toReal_pos hDpos.ne' (measure_ne_top volume _)
  constructor <;> linarith

theorem loeb_unitCircle_sum_ae_arc
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ)))
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hS : MeasurableSet (C + D))
    (hCpos : 0 < volume C) (hDpos : 0 < volume D)
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
        (φ ⁻¹' C) + (φ ⁻¹' D))
    (hperiod : ∀ z : AddCircle (1 : ℝ), z +ᵥ (C + D) =ᵐ[volume] C + D → z = 0) :
    ∃ c a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ b - a < 1 ∧
      (-(c : AddCircle (1 : ℝ)) +ᵥ (C + D)) =ᵐ[volume]
        (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) := by
  obtain ⟨hClt, hDlt⟩ := loeb_unitCircle_critical_inputs_measure_lt_one U hU q φ hφ hsurj
    C D hC hD hCpos hDpos hfull
  exact (loeb_unitCircle_measurable_sum_ae_arc_or_quasiPeriodic U hU q φ hφ hsurj
    C D hC hD hS hCpos hDpos hcomp hfull hirr hne hnoAE hperiod).resolve_left
      (not_quasiPeriodic_pair_of_proper_circle_pullbacks U hU q φ hφ hsurj C D hC hD hClt hDlt)

end Erdos335.Loeb

end
