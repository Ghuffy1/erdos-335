import Erdos335.ConvolutionTranslationBounds
import Erdos335.LinearConvolutionLimits

/-!
# Convolution periods from structured periods and a Fourier-uniform residual
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem linear_convolution_period_approximation (f w : ℕ → ℝ) (g : ℕ → ℂ)
    (Q start : ℕ) (hQ : 0 < Q) :
    linearConvolutionPeriodError f g Q start ≤
      ((∑ i ∈ range (2 * Q), ‖linearWindowConvolution (fun n => f n - w n) g Q (start + i)‖) / Q) +
      linearConvolutionPeriodError w g Q start := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hpoint (i : ℕ) :
      ‖linearWindowConvolution f g Q (start + Q + i) - linearWindowConvolution f g Q (start + i)‖ ≤
        ‖linearWindowConvolution (fun n => f n - w n) g Q (start + Q + i)‖ +
        ‖linearWindowConvolution w g Q (start + Q + i) - linearWindowConvolution w g Q (start + i)‖ +
        ‖linearWindowConvolution (fun n => f n - w n) g Q (start + i)‖ := by
    have h := approximation_translation_triangle
      (linearWindowConvolution f g Q (start + Q + i)) (linearWindowConvolution f g Q (start + i))
      (linearWindowConvolution w g Q (start + Q + i)) (linearWindowConvolution w g Q (start + i))
    simpa only [← linearWindowConvolution_sub] using h
  have hsplit := sum_range_add
    (fun i => ‖linearWindowConvolution (fun n => f n - w n) g Q (start + i)‖) Q Q
  have hsplit' : (∑ i ∈ range (2 * Q), ‖linearWindowConvolution (fun n => f n - w n) g Q (start + i)‖) =
      (∑ i ∈ range Q, ‖linearWindowConvolution (fun n => f n - w n) g Q (start + i)‖) +
      (∑ i ∈ range Q, ‖linearWindowConvolution (fun n => f n - w n) g Q (start + Q + i)‖) := by
    simpa only [two_mul, Nat.add_assoc] using hsplit
  unfold linearConvolutionPeriodError
  rw [hsplit']
  calc
    _ ≤ (∑ i ∈ range Q,
        (‖linearWindowConvolution (fun n => f n - w n) g Q (start + Q + i)‖ +
        ‖linearWindowConvolution w g Q (start + Q + i) - linearWindowConvolution w g Q (start + i)‖ +
        ‖linearWindowConvolution (fun n => f n - w n) g Q (start + i)‖)) / Q :=
      div_le_div_of_nonneg_right (sum_le_sum fun i hi => hpoint i) hQr.le
    _ = _ := by rw [sum_add_distrib, sum_add_distrib]; ring

theorem full_convolution_period_bound (f w : ℕ → ℝ) (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (n H Q : ℕ)
    (hH : 0 < H) (hHQ : H ≤ Q) (hQL : 2 * Q ≤ 3 * H) :
    linearConvolutionPeriodError f g Q (n + 3 * H) ≤
      144 * windowFourierNorm (fun t => f t - w t) n (6 * H) +
        6 * ((∑ t ∈ range (6 * H), |w (n + t + Q) - w (n + t)|) / (6 * H : ℕ)) := by
  exact (linear_convolution_period_approximation f w g Q (n + 3 * H) (hH.trans_le hHQ)).trans
    (add_le_add (convolution_two_blocks_bound (fun t => f t - w t) g hg n H Q hH hHQ hQL)
      (structured_convolution_period_bound w g hg n H Q hH hHQ hQL))

end Erdos335.IntermediateScale
