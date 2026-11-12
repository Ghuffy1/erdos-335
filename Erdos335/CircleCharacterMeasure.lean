import Erdos335.CompactCircleEquiv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Haar measure of inverse images of short circular balls
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem map_haar_unitAddCircle_eq_volume
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (φ : G →+ AddCircle (1 : ℝ)) (hφ : Continuous φ) (hsurj : Function.Surjective φ) :
    Measure.map φ μ = volume := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  have : IsProbabilityMeasure (Measure.map φ μ) := ⟨by
    rw [Measure.map_apply hφ.measurable MeasurableSet.univ]
    simp⟩
  have : (Measure.map φ μ).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure μ φ hφ hsurj
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem measure_character_closedBall_preimage_le
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (φ : G →+ AddCircle (1 : ℝ)) (hφ : Continuous φ) (hsurj : Function.Surjective φ)
    (x : AddCircle (1 : ℝ)) (r : ℝ) (hr : 0 ≤ r) :
    (μ (φ ⁻¹' Metric.closedBall x r)).toReal ≤ 2 * r := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hmap := map_haar_unitAddCircle_eq_volume μ φ hφ hsurj
  have hmeasure : μ (φ ⁻¹' Metric.closedBall x r) =
      ENNReal.ofReal (min (1 : ℝ) (2 * r)) := by
    rw [← Measure.map_apply hφ.measurable measurableSet_closedBall, hmap]
    exact AddCircle.volume_closedBall (T := (1 : ℝ)) r
  rw [hmeasure, ENNReal.toReal_ofReal (le_min zero_le_one (mul_nonneg (by norm_num) hr))]
  exact min_le_right _ _

end Erdos335.Loeb
