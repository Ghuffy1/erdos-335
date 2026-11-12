import Erdos335.LinearConvolutionTransfer

/-!
# Uniform convergence of convolutions of a Fourier-uniform residual
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem linear_convolution_l1_tendsto_zero (r : ℕ → ℝ) (g : ℕ → ℕ → ℂ)
    (hr : ∀ n, |r n| ≤ 1) (hg : ∀ s n, ‖g s n‖ ≤ 1)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hH : ∀ s, 0 < H s)
    (hscale : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (hFourier : Tendsto (fun s =>
      (∑ n ∈ range (N s), windowFourierNorm r n (2 * H s)) / N s) atTop (𝓝 0)) :
    Tendsto (fun s =>
      (∑ n ∈ range (N s), ‖linearWindowConvolution r (g s) (H s) n‖) / N s) atTop (𝓝 0) := by
  have hlim : Tendsto (fun s =>
      16 * ((∑ n ∈ range (N s), windowFourierNorm r n (2 * H s)) / N s) +
        2 * (H s : ℝ) / N s) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, mul_div_assoc] using
      (hFourier.const_mul 16).add (hscale.const_mul 2)
  apply squeeze_zero
    (fun s => div_nonneg (sum_nonneg fun n hn => norm_nonneg _) (by positivity))
    (fun s => linear_convolution_prefix_bound r (g s) hr (hg s) (N s) (H s) (hN s) (hH s)) hlim

theorem linear_convolution_energy_tendsto_zero (r : ℕ → ℝ) (g : ℕ → ℕ → ℂ)
    (hr : ∀ n, |r n| ≤ 1) (hg : ∀ s n, ‖g s n‖ ≤ 1)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hH : ∀ s, 0 < H s)
    (hscale : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (hFourier : Tendsto (fun s =>
      (∑ n ∈ range (N s), windowFourierNorm r n (2 * H s)) / N s) atTop (𝓝 0)) :
    Tendsto (fun s =>
      (∑ n ∈ range (N s), ‖linearWindowConvolution r (g s) (H s) n‖ ^ 2) / N s) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun s => div_nonneg (sum_nonneg fun n hn => sq_nonneg _) (by positivity))
    (fun s => ?_) (linear_convolution_l1_tendsto_zero r g hr hg N H hN hH hscale hFourier)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro n hn
  have hb := linearWindowConvolution_norm_le_one r (g s) hr (hg s) (H s) n (hH s)
  nlinarith [norm_nonneg (linearWindowConvolution r (g s) (H s) n)]

theorem linearWindowConvolution_sub (f w : ℕ → ℝ) (g : ℕ → ℂ) (H n : ℕ) :
    linearWindowConvolution (fun k => f k - w k) g H n =
      linearWindowConvolution f g H n - linearWindowConvolution w g H n := by
  simp only [linearWindowConvolution, Complex.ofReal_sub, sub_mul, sum_sub_distrib, sub_div]

theorem structured_convolution_energy_tendsto_zero (f w : ℕ → ℝ) (g : ℕ → ℕ → ℂ)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ n, w n ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ s n, ‖g s n‖ ≤ 1)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hH : ∀ s, 0 < H s)
    (hscale : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (hFourier : Tendsto (fun s =>
      (∑ n ∈ range (N s), windowFourierNorm (fun k => f k - w k) n (2 * H s)) / N s)
      atTop (𝓝 0)) :
    Tendsto (fun s => (∑ n ∈ range (N s),
      ‖linearWindowConvolution f (g s) (H s) n - linearWindowConvolution w (g s) (H s) n‖ ^ 2) / N s)
      atTop (𝓝 0) := by
  have hr (n : ℕ) : |f n - w n| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(hf n).1, (hf n).2, (hw n).1, (hw n).2]
  simpa only [linearWindowConvolution_sub] using
    linear_convolution_energy_tendsto_zero (fun n => f n - w n) g hr hg N H hN hH hscale hFourier

end Erdos335.IntermediateScale
