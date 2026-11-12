import Erdos335.HaarTranslation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Continuity of bounded measurable convolution

An integral-norm translation estimate on the second factor controls the
pointwise convolution difference uniformly in its argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory

namespace Erdos335.Loeb

theorem continuous_bounded_real_convolution
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (f g : G → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfbound : ∀ x, ‖f x‖ ≤ 1) (hgbound : ∀ x, ‖g x‖ ≤ 1) :
    Continuous (fun z => ∫ t, f t * g (z - t) ∂μ) := by
  have hfi (z : G) : Integrable (fun t => f t * g (z - t)) μ :=
    Integrable.of_bound (hf.mul (hg.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      1 (ae_of_all μ (fun t => by
        rw [norm_mul]
        exact (mul_le_mul (hfbound t) (hgbound _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)))
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable 1 (ae_of_all μ hgbound)
  have hbound (w z : G) :
      ‖(∫ t, f t * g (w - t) ∂μ) - ∫ t, f t * g (z - t) ∂μ‖ ≤
        ∫ u, ‖g ((w - z) + u) - g u‖ ∂μ := by
    rw [← integral_sub (hfi w) (hfi z)]
    calc
      _ ≤ ∫ t, ‖f t * g (w - t) - f t * g (z - t)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, ‖g (w - t) - g (z - t)‖ ∂μ := by
        apply integral_mono ((hfi w).sub (hfi z)).norm
          ((hgi.comp_sub_left w).sub (hgi.comp_sub_left z)).norm
        intro t
        change ‖f t * g (w - t) - f t * g (z - t)‖ ≤ ‖g (w - t) - g (z - t)‖
        rw [← mul_sub, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hfbound t)
      _ = _ := by
        have hshift := integral_sub_left_eq_self (fun u => ‖g ((w - z) + u) - g u‖) μ z
        have heq (t : G) : (w - z) + (z - t) = w - t := by abel
        simpa only [heq] using hshift
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim := (tendsto_integral_norm_add_sub_zero μ g hgi).comp
    (show Tendsto (fun w : G => w - z) (𝓝 z) (𝓝 0) from by
      have hc : Continuous (fun w : G => w - z) := continuous_id.sub continuous_const
      simpa only [sub_self] using hc.tendsto z)
  exact squeeze_zero (fun w => norm_nonneg _) (fun w => hbound w z) hlim

theorem isOpen_positive_bounded_real_convolution
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (f g : G → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfbound : ∀ x, ‖f x‖ ≤ 1) (hgbound : ∀ x, ‖g x‖ ≤ 1) :
    IsOpen {z | 0 < ∫ t, f t * g (z - t) ∂μ} :=
  isOpen_lt continuous_const (continuous_bounded_real_convolution μ f g hf hg hfbound hgbound)

end Erdos335.Loeb
