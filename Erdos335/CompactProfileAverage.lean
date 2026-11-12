import Erdos335.CompactIntersectionProfile
import Mathlib.MeasureTheory.Integral.Average

/-!
# Small positive values of an intersection profile

The first moment method selects a positive overlap no larger than the
average over its positive support. A lower bound for the measure of that
support then yields the shrinking estimate in the e-transform argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem exists_positive_le_support_average
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]
    (f : G → ℝ) (hf : Integrable f μ) (hnonneg : ∀ x, 0 ≤ f x)
    (hpositive : 0 < ∫ x, f x ∂μ)
    (hsupport : MeasurableSet {x | 0 < f x}) :
    ∃ x, 0 < f x ∧ f x ≤ (∫ x, f x ∂μ) / (μ {x | 0 < f x}).toReal := by
  let S := {x | 0 < f x}
  have hset : Function.support f = S := by
    ext x
    change f x ≠ 0 ↔ 0 < f x
    exact ⟨fun hn => lt_of_le_of_ne (hnonneg x) hn.symm, fun hp => hp.ne'⟩
  have hSpos : 0 < μ S := by
    rw [← hset]
    exact (integral_pos_iff_support_of_nonneg hnonneg hf).mp hpositive
  obtain ⟨x, hxS, hx⟩ := exists_le_setAverage hSpos.ne' (measure_ne_top μ S) hf.integrableOn
  have hindicator : S.indicator f = f := by
    funext y
    by_cases hy : y ∈ S
    · exact Set.indicator_of_mem hy f
    · have hyzero : f y = 0 := le_antisymm (le_of_not_gt hy) (hnonneg y)
      simp only [Set.indicator_of_notMem hy, hyzero]
  have hintegral : (∫ y in S, f y ∂μ) = ∫ y, f y ∂μ := by
    rw [← integral_indicator hsupport, hindicator]
  refine ⟨x, hxS, ?_⟩
  simpa only [setAverage_eq, measureReal_def, smul_eq_mul, hintegral, div_eq_mul_inv, mul_comm] using hx

theorem small_intersection_average_bound
    (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) (hs : a + b ≤ s) :
    (a * b) / s ≤ (1 - b) * b := by
  have habpos : 0 < a + b := add_pos ha hb
  calc
    (a * b) / s ≤ (a * b) / (a + b) :=
      div_le_div_of_nonneg_left (mul_nonneg ha.le hb.le) habpos hs
    _ ≤ (1 - b) * b := by
      apply (div_le_iff₀ habpos).mpr
      nlinarith [mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hab)]

theorem exists_small_positive_intersection
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hApos : 0 < (μ A).toReal) (hBpos : 0 < (μ B).toReal)
    (htotal : (μ A).toReal + (μ B).toReal ≤ 1)
    (hsupport : (μ A).toReal + (μ B).toReal ≤
      (μ {e | 0 < compactIntersectionProfile μ A B e}).toReal) :
    ∃ e, 0 < compactIntersectionProfile μ A B e ∧
      compactIntersectionProfile μ A B e ≤ (1 - (μ B).toReal) * (μ B).toReal := by
  let f := compactIntersectionProfile μ A B
  have hf := continuous_compactIntersectionProfile μ A B hA hB
  have hfnonneg : ∀ x, 0 ≤ f x := fun _ => ENNReal.toReal_nonneg
  have hfbound : ∀ x, ‖f x‖ ≤ (μ A).toReal := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg x)]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono inter_subset_left)
  have hfi : Integrable f μ := Integrable.of_bound hf.measurable.aestronglyMeasurable
    (μ A).toReal (ae_of_all μ hfbound)
  have hmean : (∫ x, f x ∂μ) = (μ A).toReal * (μ B).toReal :=
    integral_compactIntersectionProfile μ A B hA hB
  obtain ⟨e, hepos, he⟩ := exists_positive_le_support_average μ f hfi hfnonneg
    (hmean.symm ▸ mul_pos hApos hBpos) (isOpen_lt continuous_const hf).measurableSet
  refine ⟨e, hepos, he.trans ?_⟩
  rw [hmean]
  exact small_intersection_average_bound _ _ _ hApos hBpos htotal hsupport

end Erdos335.Loeb
