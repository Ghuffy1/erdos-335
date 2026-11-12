import Erdos335.LoebContinuousIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic

/-!
# Uniformly bounded complex internal functions

The real integral transfer applies to real linear components of the compact
complex ball. Combining the two components gives the complex integral transfer.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators

namespace Erdos335.Loeb

variable {I : Type*} {X : I → Type*}

noncomputable def boundedComplexFunction (U : Ultrafilter I) (f : ∀ i, X i → ℂ)
    (M : ℝ) (h : ∀ i x, ‖f i x‖ ≤ M) : (U : Filter I).Product X → ℂ :=
  fun x => (ultralimitFunction U
    (fun i y => (⟨f i y, by simpa only [Metric.mem_closedBall, dist_zero_right] using h i y⟩ :
      Metric.closedBall (0 : ℂ) M)) x).val

theorem boundedComplexFunction_bound (U : Ultrafilter I) (f : ∀ i, X i → ℂ)
    (M : ℝ) (h : ∀ i x, ‖f i x‖ ≤ M) (x : (U : Filter I).Product X) :
    ‖boundedComplexFunction U f M h x‖ ≤ M := by
  unfold boundedComplexFunction
  exact (by simpa only [Metric.mem_closedBall, dist_zero_right] using
    (ultralimitFunction U
      (fun i y => (⟨f i y, by simpa only [Metric.mem_closedBall, dist_zero_right] using h i y⟩ :
        Metric.closedBall (0 : ℂ) M)) x).property)

theorem measurable_boundedComplexFunction
    {Y : ℕ → Type*} [∀ n, Finite (Y n)] [∀ n, Nonempty (Y n)]
    (U : Ultrafilter ℕ) (f : ∀ n, Y n → ℂ) (M : ℝ) (h : ∀ n x, ‖f n x‖ ≤ M) :
    @Measurable ((U : Filter ℕ).Product Y) ℂ (loebMeasurableSpace U) _
      (boundedComplexFunction U f M h) :=
  continuous_subtype_val.measurable.comp (measurable_ultralimitFunction U _)

theorem integrable_boundedComplexFunction
    {Y : ℕ → Type*} [∀ n, Finite (Y n)] [∀ n, Nonempty (Y n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, Y n → ℂ) (M : ℝ) (h : ∀ n x, ‖f n x‖ ≤ M) :
    Integrable (boundedComplexFunction U f M h) (loebMeasure U hU) := by
  let : MeasurableSpace ((U : Filter ℕ).Product Y) := loebMeasurableSpace U
  let : IsProbabilityMeasure (loebMeasure (X := Y) U hU) := isProbabilityMeasure_loebMeasure U hU
  exact Integrable.of_bound (measurable_boundedComplexFunction U f M h).aestronglyMeasurable
    M (ae_of_all _ (boundedComplexFunction_bound U f M h))

theorem tendsto_boundedComplex_component_averages
    {Y : ℕ → Type*} [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, Y n → ℂ) (M : ℝ) (h : ∀ n x, ‖f n x‖ ≤ M) (L : ℂ →L[ℝ] ℝ) :
    Tendsto (fun n => L ((Nat.card (Y n) : ℝ)⁻¹ • ∑ x : Y n, f n x))
      (U : Filter ℕ) (𝓝 (L (∫ x, boundedComplexFunction U f M h x ∂loebMeasure U hU))) := by
  let : MeasurableSpace ((U : Filter ℕ).Product Y) := loebMeasurableSpace U
  let F : ∀ n, Y n → Metric.closedBall (0 : ℂ) M :=
    fun n x => ⟨f n x, by simpa only [Metric.mem_closedBall, dist_zero_right] using h n x⟩
  have ht := tendsto_continuous_coordinate_averages U hU F
    (fun z => L z.val) (L.continuous.comp continuous_subtype_val)
  have hi := L.integral_comp_comm (integrable_boundedComplexFunction U hU f M h)
  rw [← hi]
  simpa only [F, boundedComplexFunction, map_smul, map_sum, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using ht

theorem tendsto_boundedComplexFunction_averages
    {Y : ℕ → Type*} [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, Y n → ℂ) (M : ℝ) (h : ∀ n x, ‖f n x‖ ≤ M) :
    Tendsto (fun n => (Nat.card (Y n) : ℝ)⁻¹ • ∑ x : Y n, f n x)
      (U : Filter ℕ) (𝓝 (∫ x, boundedComplexFunction U f M h x ∂loebMeasure U hU)) := by
  have hr := tendsto_boundedComplex_component_averages U hU f M h RCLike.reCLM
  have hi := tendsto_boundedComplex_component_averages U hU f M h RCLike.imCLM
  have hrC := (Complex.continuous_ofReal.tendsto _).comp hr
  have hiC := (Complex.continuous_ofReal.tendsto _).comp hi
  have hsum := hrC.add (hiC.mul (tendsto_const_nhds (x := Complex.I)))
  have hdecomp (z : ℂ) : (RCLike.re z : ℂ) + (RCLike.im z : ℂ) * Complex.I = z :=
    RCLike.re_add_im z
  simpa only [Function.comp_apply, RCLike.reCLM_apply, RCLike.imCLM_apply,
    hdecomp] using hsum

end Erdos335.Loeb
