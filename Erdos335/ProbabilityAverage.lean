import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-!
# Integral bound for a probability average

Fubini and the norm inequality for the Bochner integral give the contraction
estimate used below for averages of translates.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

theorem integral_norm_probability_average_le
    {X U E : Type*} [MeasurableSpace X] [MeasurableSpace U]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [SFinite μ] (ν : Measure U) [IsProbabilityMeasure ν]
    (F : X → U → E) (hF : Integrable (Function.uncurry F) (μ.prod ν)) :
    (∫ x, ‖∫ u, F x u ∂ν‖ ∂μ) ≤ ∫ u, ∫ x, ‖F x u‖ ∂μ ∂ν := by
  calc
    _ ≤ ∫ x, ∫ u, ‖F x u‖ ∂ν ∂μ := by
      exact integral_mono hF.integral_prod_left.norm hF.integral_norm_prod_left
        (fun x => norm_integral_le_integral_norm _)
    _ = _ := integral_integral_swap hF.norm

theorem integral_norm_probability_average_sub_le
    {X U E : Type*} [MeasurableSpace X] [MeasurableSpace U]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure U) [IsProbabilityMeasure ν]
    (F : X → U → E) (f : X → E)
    (hF : Integrable (Function.uncurry F) (μ.prod ν)) (hf : Integrable f μ) :
    (∫ x, ‖(∫ u, F x u ∂ν) - f x‖ ∂μ) ≤
      ∫ u, ∫ x, ‖F x u - f x‖ ∂μ ∂ν := by
  have hsub : Integrable (fun p : X × U => F p.1 p.2 - f p.1) (μ.prod ν) :=
    hF.sub (hf.comp_fst ν)
  have heq : (fun x => ∫ u, F x u - f x ∂ν) =ᵐ[μ]
      (fun x => (∫ u, F x u ∂ν) - f x) := by
    filter_upwards [hF.prod_right_ae] with x hx
    change Integrable (F x) ν at hx
    rw [integral_sub hx (integrable_const _), integral_const, probReal_univ, one_smul]
  calc
    _ = ∫ x, ‖∫ u, F x u - f x ∂ν‖ ∂μ := integral_congr_ae (heq.fun_comp norm).symm
    _ ≤ _ := integral_norm_probability_average_le μ ν (fun x u => F x u - f x) hsub

theorem tendstoInMeasure_of_integral_norm_tendsto_zero
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (F : ℕ → X → E) (f : X → E)
    (hF : ∀ n, Integrable (F n - f) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ F atTop f := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
  have heq (n : ℕ) : eLpNorm (F n - f) 1 μ = ENNReal.ofReal (∫ x, ‖F n x - f x‖ ∂μ) := by
    rw [(memLp_one_iff_integrable.mpr (hF n)).eLpNorm_eq_integral_rpow_norm (by simp) (by simp)]
    simp
  simp_rw [heq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp hlim

end Erdos335.Loeb
