import Erdos335.LoebConditionalFactor
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Testing a conditional factor against complex functions

The defining conditional expectation identity also preserves complex
weighted integrals. This supplies the Fourier coefficients of the positive
input representatives on a compact factor.
-/

set_option autoImplicit false

open Filter Set MeasureTheory

namespace Erdos335.Loeb

theorem integral_smul_conditional_factor
    {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure A) [IsFiniteMeasure μ] (q : A → B) (hq : Measurable q)
    (f : A → ℝ) (hf : Integrable f μ) (g : B → ℝ) (hg : StronglyMeasurable g)
    (heq : μ[f | mB.comap q] =ᵐ[μ] g ∘ q)
    (w : B → ℂ) (hw : StronglyMeasurable w)
    (hprod : Integrable (fun x => f x • w (q x)) μ) :
    (∫ x, f x • w (q x) ∂μ) = ∫ y, g y • w y ∂Measure.map q μ := by
  have hm : mB.comap q ≤ mA := hq.comap_le
  have hwq : StronglyMeasurable[mB.comap q] (fun x => w (q x)) :=
    hw.comp_measurable (show @Measurable A B (mB.comap q) mB q from
      measurable_iff_comap_le.mpr le_rfl)
  have hcond := condExp_bilin_of_stronglyMeasurable_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hwq hprod hf
  calc
    (∫ x, f x • w (q x) ∂μ) =
        ∫ x, μ[(fun t => f t • w (q t)) | mB.comap q] x ∂μ := (integral_condExp hm).symm
    _ = ∫ x, μ[f | mB.comap q] x • w (q x) ∂μ := integral_congr_ae hcond
    _ = ∫ x, g (q x) • w (q x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [show μ[f | mB.comap q] x = g (q x) from hx]
    _ = ∫ y, g y • w y ∂Measure.map q μ :=
      (integral_map hq.aemeasurable (hg.smul hw).aestronglyMeasurable).symm

end Erdos335.Loeb
