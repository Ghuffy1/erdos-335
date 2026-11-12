import Erdos335.LoebConditionalTests
import Mathlib.Analysis.Complex.Basic

/-!
# Fourier tests under a measurable factor

The pushforward formula transfers tests of a factored function. Conditional
expectation transfers the same tests for the original real input, when the
test function is bounded by one.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ComplexConjugate

namespace Erdos335.Loeb

theorem integral_factor_conjugate_test
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (q : A → B) (hq : Measurable q)
    (f : A → ℂ) (F : B → ℂ) (hF : StronglyMeasurable F)
    (heq : f =ᵐ[μ] F ∘ q) (p : B → ℂ) (hp : StronglyMeasurable p) :
    (∫ y, F y * conj (p y) ∂Measure.map q μ) =
      ∫ x, f x * conj (p (q x)) ∂μ := by
  have htest : StronglyMeasurable (fun y => F y * conj (p y)) := hF.mul hp.star
  rw [integral_map hq.aemeasurable htest.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  exact congrArg (fun z : ℂ => z * conj (p (q x))) hx.symm

theorem integral_conditional_conjugate_test
    {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure A) [IsFiniteMeasure μ] (q : A → B) (hq : Measurable q)
    (f : A → ℝ) (hf : Integrable f μ) (F : B → ℝ) (hF : StronglyMeasurable F)
    (heq : μ[f | mB.comap q] =ᵐ[μ] F ∘ q)
    (p : B → ℂ) (hp : StronglyMeasurable p) (hbound : ∀ y, ‖p y‖ ≤ 1) :
    (∫ x, (f x : ℂ) * conj (p (q x)) ∂μ) =
      ∫ y, (F y : ℂ) * conj (p y) ∂Measure.map q μ := by
  have htest : StronglyMeasurable (fun x => conj (p (q x))) := hp.star.comp_measurable hq
  have hprod : Integrable (fun x => f x • conj (p (q x))) μ := by
    apply hf.mono (hf.aestronglyMeasurable.smul htest.aestronglyMeasurable)
    exact ae_of_all μ (fun x => by
      change ‖f x • conj (p (q x))‖ ≤ ‖f x‖
      simpa [norm_smul] using
        mul_le_mul_of_nonneg_left (hbound (q x)) (norm_nonneg (f x)))
  have h := integral_smul_conditional_factor μ q hq f hf F hF heq
    (fun y => conj (p y)) hp.star hprod
  simp only [RCLike.real_smul_eq_coe_mul] at h
  exact h

end Erdos335.Loeb
