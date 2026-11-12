import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Closing a measurable factor under mean-square limits

Convergence in measure of functions on one factor gives an almost-everywhere
factorization of the limit. Square-integral convergence supplies the required
convergence in measure.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

theorem exists_factor_of_tendstoInMeasure
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (q : A → B) (P : ℕ → B → ℂ) (f : A → ℂ)
    (hP : ∀ n, StronglyMeasurable (P n))
    (hlim : TendstoInMeasure μ (fun n x => P n (q x)) atTop f) :
    ∃ g : B → ℂ, StronglyMeasurable g ∧ f =ᵐ[μ] g ∘ q := by
  obtain ⟨ns, _, hns⟩ := hlim.exists_seq_tendsto_ae
  let g : B → ℂ := fun y => limUnder atTop (fun n => P (ns n) y)
  refine ⟨g, StronglyMeasurable.limUnder (fun n => hP (ns n)), ?_⟩
  filter_upwards [hns] with x hx
  exact hx.limUnder_eq.symm

theorem eLpNorm_two_eq_sqrt_integral
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (f : A → ℂ)
    (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow]
  norm_num

theorem tendstoInMeasure_of_sqIntegral_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (f : ℕ → A → ℂ) (g : A → ℂ)
    (hmem : ∀ n, MemLp (f n - g) 2 μ)
    (hlim : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop g := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at hsqrt
  have hof := (ENNReal.continuous_ofReal.tendsto 0).comp hsqrt
  simpa only [eLpNorm_two_eq_sqrt_integral μ _ (hmem _), Pi.sub_apply,
    Real.sqrt_zero, ENNReal.ofReal_zero, Function.comp_def] using hof

end Erdos335.Loeb
