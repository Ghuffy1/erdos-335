import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Complex.Circle

/-!
# Convolution coefficients for invariant measures

Circle-valued characters turn convolution into multiplication of Fourier
coefficients. The argument uses Mathlib's invariant-measure convolution
integral theorem and applies in particular to compact Haar groups.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology ComplexConjugate

namespace Erdos335.Loeb

theorem integral_convolution_character
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]
    (χ : AddChar G Circle) (hχ : Measurable (fun x => (χ x : ℂ)))
    (f g : G → ℂ) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, (∫ t, f t * g (x - t) ∂μ) * conj (χ x : ℂ) ∂μ) =
      (∫ x, f x * conj (χ x : ℂ) ∂μ) * (∫ x, g x * conj (χ x : ℂ) ∂μ) := by
  let w : G → ℂ := fun x => conj (χ x : ℂ)
  have hw : StronglyMeasurable w :=
    (continuous_star.measurable.comp hχ).stronglyMeasurable
  have hfw : Integrable (fun x => f x * w x) μ := by
    apply hf.mono (hf.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    exact ae_of_all μ (fun x => by simp [w])
  have hgw : Integrable (fun x => g x * w x) μ := by
    apply hg.mono (hg.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    exact ae_of_all μ (fun x => by simp [w])
  have hwmul (x t : G) : w t * w (x - t) = w x := by
    change conj (χ t : ℂ) * conj (χ (x - t) : ℂ) = conj (χ x : ℂ)
    rw [← map_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    abel
  have hpoint (x : G) : (∫ t, f t * g (x - t) ∂μ) * w x =
      ∫ t, (f t * w t) * (g (x - t) * w (x - t)) ∂μ := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all μ (fun t => by rw [← hwmul x t]; ring)
  change (∫ x, (∫ t, f t * g (x - t) ∂μ) * w x ∂μ) = _
  simp_rw [hpoint]
  exact integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hfw hgw

end Erdos335.Loeb
