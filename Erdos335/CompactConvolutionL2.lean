import Erdos335.CompactFourierConvolution
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Mean-square bounds for compact convolution factors

The convolution of two unit-ball-valued functions on a probability group is
unit-ball-valued. Measurability therefore gives a square-integrable function.
Square integrability also descends through a measurable factor.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

theorem probability_convolution_norm_le_one
    {G : Type*} [AddGroup G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (f g : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (x : G) :
    ‖∫ t, f t * g (x - t) ∂μ‖ ≤ 1 := by
  have hbound : ∀ᵐ t ∂μ, ‖f t * g (x - t)‖ ≤ 1 := ae_of_all μ (fun t => by
    rw [norm_mul]
    exact (mul_le_mul (hf t) (hg (x - t)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
  simpa using norm_integral_le_of_norm_le_const hbound

theorem probability_convolution_memLp_two
    {G : Type*} [AddGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddRightInvariant]
    (f g : G → ℂ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfbound : ∀ x, ‖f x‖ ≤ 1) (hgbound : ∀ x, ‖g x‖ ≤ 1) :
    MemLp (fun x => ∫ t, f t * g (x - t) ∂μ) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun x => ∫ t, f t * g (x - t) ∂μ) μ :=
    hf.convolution (L := ContinuousLinearMap.mul ℂ ℂ) hg
  exact MemLp.of_bound hmeas 1 (ae_of_all μ (probability_convolution_norm_le_one μ f g hfbound hgbound))

theorem factor_memLp_two_of_ae_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (q : A → B) (hq : Measurable q)
    (f : A → ℂ) (hf : MemLp f 2 μ) (F : B → ℂ) (hF : StronglyMeasurable F)
    (heq : f =ᵐ[μ] F ∘ q) : MemLp F 2 (Measure.map q μ) := by
  exact (memLp_map_measure_iff hF.aestronglyMeasurable hq.aemeasurable).mpr
    ((memLp_congr_ae heq).mp hf)

end Erdos335.Loeb
