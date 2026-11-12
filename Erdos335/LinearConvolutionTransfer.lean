import Erdos335.LinearWindowConvolution
import Erdos335.WindowShiftAverages

/-!
# Residual Fourier uniformity transfers to linear window convolution
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_sum_le_shifted_prefix (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C) (N i : ℕ) :
    (∑ n ∈ range N, f n) ≤ (∑ n ∈ range N, f (n + i)) + C * i := by
  have hleft := sum_range_add f i N
  have hright := sum_range_add f N i
  rw [Nat.add_comm i N] at hleft
  have hnonneg : 0 ≤ ∑ n ∈ range i, f (N + n) := sum_nonneg fun n hn => (hf _).1
  have hearly : (∑ n ∈ range i, f n) ≤ C * i := by
    exact (sum_le_sum fun n hn => (hf n).2).trans_eq (by simp; ring)
  have heq : (∑ n ∈ range N, f n) + (∑ n ∈ range i, f (N + n)) =
      (∑ n ∈ range i, f n) + (∑ n ∈ range N, f (n + i)) := by
    simpa only [Nat.add_comm] using hright.symm.trans hleft
  linarith

theorem prefix_average_le_shifted_windows (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C) (N H : ℕ) (hN : 0 < N) (hH : 0 < H) :
    (∑ n ∈ range N, f n) / N ≤
      (∑ n ∈ range N, (∑ i ∈ range H, f (n + H + i)) / H) / N +
        2 * C * (H : ℝ) / N := by
  have hC : 0 ≤ C := (hf 0).1.trans (hf 0).2
  have hsum : (H : ℝ) * (∑ n ∈ range N, f n) ≤
      (∑ n ∈ range N, ∑ i ∈ range H, f (n + H + i)) + (H : ℝ) * (2 * C * H) := by
    calc
      _ = ∑ _i ∈ range H, (∑ n ∈ range N, f n) := by simp
      _ ≤ ∑ i ∈ range H, ((∑ n ∈ range N, f (n + H + i)) + 2 * C * H) := by
        apply sum_le_sum
        intro i hi
        have hp := prefix_sum_le_shifted_prefix f C hf N (H + i)
        have hb : C * ((H + i : ℕ) : ℝ) ≤ 2 * C * H := by
          have hi' : (i : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hi).le
          push_cast
          nlinarith
        simpa only [Nat.add_assoc] using hp.trans (add_le_add le_rfl hb)
      _ = _ := by rw [sum_add_distrib, sum_comm]; simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hd := div_le_div_of_nonneg_right hsum (mul_pos hHr hNr).le
  rw [← sum_div]
  convert hd using 1 <;> field_simp [hNr.ne', hHr.ne'] <;> ring

theorem linearWindowConvolution_norm_le_one (r : ℕ → ℝ) (g : ℕ → ℂ)
    (hr : ∀ n, |r n| ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (H n : ℕ) (hH : 0 < H) :
    ‖linearWindowConvolution r g H n‖ ≤ 1 := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  unfold linearWindowConvolution
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hHr).mpr
  calc
    _ ≤ ∑ m ∈ range H, ‖(r (n - m) : ℂ) * g m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ range H, (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_one₀ (hr _) (norm_nonneg _) (hg m)
    _ = _ := by simp

theorem linear_convolution_prefix_bound (r : ℕ → ℝ) (g : ℕ → ℂ)
    (hr : ∀ n, |r n| ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (N H : ℕ)
    (hN : 0 < N) (hH : 0 < H) :
    (∑ n ∈ range N, ‖linearWindowConvolution r g H n‖) / N ≤
      16 * ((∑ n ∈ range N, windowFourierNorm r n (2 * H)) / N) + 2 * (H : ℝ) / N := by
  have hpre := prefix_average_le_shifted_windows (fun n => ‖linearWindowConvolution r g H n‖) 1
    (fun n => ⟨norm_nonneg _, linearWindowConvolution_norm_le_one r g hr hg H n hH⟩) N H hN hH
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlocal : (∑ n ∈ range N,
      (∑ i ∈ range H, ‖linearWindowConvolution r g H (n + H + i)‖) / H) / N ≤
      16 * ((∑ n ∈ range N, windowFourierNorm r n (2 * H)) / N) := by
    calc
      _ ≤ (∑ n ∈ range N, 16 * windowFourierNorm r n (2 * H)) / N :=
        div_le_div_of_nonneg_right
          (sum_le_sum fun n hn => linear_window_convolution_average_le r g hg n H hH) hNr.le
      _ = _ := by rw [← mul_sum]; ring
  simpa only [mul_one] using hpre.trans (add_le_add hlocal le_rfl)

end Erdos335.IntermediateScale
