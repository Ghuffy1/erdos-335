import Erdos335.FullConvolutionPeriodBound
import Erdos335.IndicatorWindowConvolution

/-!
# Vanishing average convolution-translation errors
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem convolution_period_average_tendsto_zero
    (f w : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℂ) (hg : ∀ s n m, ‖g s n m‖ ≤ 1)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hH : ∀ s, 0 < H s)
    (Q : ℕ → ℕ → ℕ)
    (hQ : ∀ᶠ s in atTop, ∀ n, H s ≤ Q s n ∧ 2 * Q s n ≤ 3 * H s)
    (hFourier : Tendsto (fun s => (∑ n ∈ range (N s),
      windowFourierNorm (fun t => f t - w t) n (6 * H s)) / N s) atTop (𝓝 0))
    (hperiod : Tendsto (fun s => averagedWindowTranslationError (fun n => (w n : ℂ))
      (Q s) (N s) (6 * H s)) atTop (𝓝 0)) :
    Tendsto (fun s => (∑ n ∈ range (N s),
      linearConvolutionPeriodError f (g s n) (Q s n) (n + 3 * H s)) / N s) atTop (𝓝 0) := by
  have hlim : Tendsto (fun s =>
      144 * ((∑ n ∈ range (N s), windowFourierNorm (fun t => f t - w t) n (6 * H s)) / N s) +
        6 * averagedWindowTranslationError (fun n => (w n : ℂ)) (Q s) (N s) (6 * H s))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hFourier.const_mul 144).add (hperiod.const_mul 6)
  apply squeeze_zero' (Eventually.of_forall fun s => by
      unfold linearConvolutionPeriodError
      positivity) ?_ hlim
  filter_upwards [hQ] with s hs
  have hNr : (0 : ℝ) < N s := by exact_mod_cast hN s
  calc
    _ ≤ (∑ n ∈ range (N s),
        (144 * windowFourierNorm (fun t => f t - w t) n (6 * H s) +
          6 * ((∑ t ∈ range (6 * H s), |w (n + t + Q s n) - w (n + t)|) / (6 * H s : ℕ)))) / N s :=
      div_le_div_of_nonneg_right (sum_le_sum fun n hn =>
        full_convolution_period_bound f w (g s n) (hg s n) n (H s) (Q s n) (hH s) (hs n).1 (hs n).2)
        hNr.le
    _ = _ := by
      unfold averagedWindowTranslationError
      simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        sum_add_distrib, ← mul_sum, add_div, mul_div_assoc]

theorem indicator_convolution_period_error_bound (A B : Set ℕ) (w : ℕ → ℝ)
    (n H Q : ℕ) [NeZero Q] (hH : 0 < H) (hHQ : H ≤ Q) (hQL : 2 * Q ≤ 3 * H) :
    convolutionTranslationError A B (n + 3 * H) Q / (Q : ℝ) ^ 2 ≤
      144 * windowFourierNorm (fun t => A.indicator (fun _ => (1 : ℝ)) t - w t) n (6 * H) +
        6 * ((∑ t ∈ range (6 * H), |w (n + t + Q) - w (n + t)|) / (6 * H : ℕ)) := by
  classical
  rw [convolutionTranslationError_eq_linear A B Q (n + 3 * H) (by omega)]
  apply full_convolution_period_bound _ w _ _ n H Q hH hHQ hQL
  intro m
  by_cases hm : m ∈ B <;> simp [hm]

end Erdos335.IntermediateScale
