import Erdos335.LinearConvolutionLimits
import Erdos335.WindowFourierExtension

/-!
# Uniform convolution control with a window-dependent length and second input
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

noncomputable def variableConvolutionAverage (r : ℕ → ℝ) (g : ℕ → ℕ → ℂ)
    (Q : ℕ → ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, (∑ i ∈ range (Q n),
    ‖linearWindowConvolution r (g n) (Q n) (n + Q n + i)‖) / Q n) / N

theorem variable_convolution_average_bound (r : ℕ → ℝ) (g : ℕ → ℕ → ℂ)
    (hr : ∀ n, |r n| ≤ 1) (hg : ∀ n m, ‖g n m‖ ≤ 1)
    (Q : ℕ → ℕ) (N H : ℕ) (hN : 0 < N) (hH : 0 < H)
    (ε : ℝ) (hε : 0 ≤ ε) (hQ : ∀ n, H ≤ Q n ∧ (Q n : ℝ) ≤ (1 + ε) * H) :
    variableConvolutionAverage r g Q N ≤
      16 * ((∑ n ∈ range N, windowFourierNorm r n (2 * H)) / N) + 16 * ε := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp (n : ℕ) : (∑ i ∈ range (Q n),
      ‖linearWindowConvolution r (g n) (Q n) (n + Q n + i)‖) / Q n ≤
      16 * windowFourierNorm r n (2 * H) + 16 * ε := by
    have hqpos : 0 < Q n := hH.trans_le (hQ n).1
    have hsize : ((2 * Q n : ℕ) : ℝ) ≤ (1 + ε) * (2 * H : ℕ) := by
      push_cast
      nlinarith [(hQ n).2]
    have hnorm := windowFourierNorm_extend_ratio r hr n (2 * H) (2 * Q n)
      (by omega) (Nat.mul_le_mul_left 2 (hQ n).1) ε hε hsize
    exact (linear_window_convolution_average_le r (g n) (hg n) n (Q n) hqpos).trans (by linarith)
  unfold variableConvolutionAverage
  calc
    _ ≤ (∑ n ∈ range N, (16 * windowFourierNorm r n (2 * H) + 16 * ε)) / N :=
      div_le_div_of_nonneg_right (sum_le_sum fun n hn => hp n) hNr.le
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum]
      simp only [sum_const, card_range, nsmul_eq_mul]
      field_simp

theorem variable_convolution_average_tendsto_zero
    (r : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℂ) (Q : ℕ → ℕ → ℕ)
    (hr : ∀ n, |r n| ≤ 1) (hg : ∀ s n m, ‖g s n m‖ ≤ 1)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hH : ∀ s, 0 < H s)
    (ε : ℕ → ℝ) (hε : ∀ s, 0 ≤ ε s) (hεlim : Tendsto ε atTop (𝓝 0))
    (hQ : ∀ᶠ s in atTop, ∀ n, H s ≤ Q s n ∧ (Q s n : ℝ) ≤ (1 + ε s) * H s)
    (hFourier : Tendsto (fun s =>
      (∑ n ∈ range (N s), windowFourierNorm r n (2 * H s)) / N s) atTop (𝓝 0)) :
    Tendsto (fun s => variableConvolutionAverage r (g s) (Q s) (N s)) atTop (𝓝 0) := by
  have hbound : Tendsto (fun s =>
      16 * ((∑ n ∈ range (N s), windowFourierNorm r n (2 * H s)) / N s) + 16 * ε s)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hFourier.const_mul 16).add (hεlim.const_mul 16)
  apply squeeze_zero' (Eventually.of_forall fun s => by
      unfold variableConvolutionAverage
      positivity) ?_ hbound
  filter_upwards [hQ] with s hs
  exact variable_convolution_average_bound r (g s) hr (hg s) (Q s) (N s) (H s) (hN s) (hH s)
    (ε s) (hε s) hs

end Erdos335.IntermediateScale
