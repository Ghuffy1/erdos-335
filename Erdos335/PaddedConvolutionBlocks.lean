import Erdos335.LinearWindowConvolution

/-!
# Two consecutive convolution blocks inside one fixed larger window
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

noncomputable def truncatedConvolutionInput (g : ℕ → ℂ) (Q : ℕ) (m : ℕ) : ℂ :=
  if m < Q then g m else 0

theorem truncatedConvolutionInput_norm_le (g : ℕ → ℂ) (Q : ℕ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (m : ℕ) : ‖truncatedConvolutionInput g Q m‖ ≤ 1 := by
  unfold truncatedConvolutionInput
  split_ifs
  · exact hg m
  · simp

theorem linearWindowConvolution_padding (r : ℕ → ℝ) (g : ℕ → ℂ)
    (Q L n : ℕ) (_hQ : 0 < Q) (hL : 0 < L) (hQL : Q ≤ L) :
    linearWindowConvolution r g Q n = ((L : ℂ) / Q) *
      linearWindowConvolution r (truncatedConvolutionInput g Q) L n := by
  have hfilter : (range L).filter (fun m => m < Q) = range Q := by
    ext m
    simp only [mem_filter, mem_range]
    omega
  have hsum : (∑ m ∈ range L, (r (n - m) : ℂ) * truncatedConvolutionInput g Q m) =
      ∑ m ∈ range Q, (r (n - m) : ℂ) * g m := by
    simp only [truncatedConvolutionInput, mul_ite, mul_zero]
    rw [← sum_filter, hfilter]
  unfold linearWindowConvolution
  rw [hsum]
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

theorem convolution_two_blocks_bound (r : ℕ → ℝ) (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (n H Q : ℕ) (hH : 0 < H) (hHQ : H ≤ Q) (hQL : 2 * Q ≤ 3 * H) :
    (∑ i ∈ range (2 * Q), ‖linearWindowConvolution r g Q (n + 3 * H + i)‖) / Q ≤
      144 * windowFourierNorm r n (6 * H) := by
  let L := 3 * H
  have hL : 0 < L := by dsimp [L]; omega
  have hQ : 0 < Q := hH.trans_le hHQ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hQL' : Q ≤ L := by dsimp [L]; omega
  let v := fun i => ‖linearWindowConvolution r (truncatedConvolutionInput g Q) L (n + L + i)‖
  have hlocal : (∑ i ∈ range L, v i) / L ≤ 16 * windowFourierNorm r n (6 * H) := by
    simpa only [v, L, show 2 * (3 * H) = 6 * H by omega] using
      linear_window_convolution_average_le r (truncatedConvolutionInput g Q)
        (truncatedConvolutionInput_norm_le g Q hg) n L hL
  have hsub : (∑ i ∈ range (2 * Q), v i) ≤ ∑ i ∈ range L, v i :=
    sum_le_sum_of_subset_of_nonneg (range_mono hQL) (fun i hi hnot => norm_nonneg _)
  have hpoint (i : ℕ) : ‖linearWindowConvolution r g Q (n + L + i)‖ = ((L : ℝ) / Q) * v i := by
    rw [linearWindowConvolution_padding r g Q L (n + L + i) hQ hL hQL', norm_mul,
      norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hratio : (L : ℝ) / Q ≤ 3 := by
    apply (div_le_iff₀ hQr).mpr
    dsimp [L]
    exact_mod_cast Nat.mul_le_mul_left 3 hHQ
  change (∑ i ∈ range (2 * Q), ‖linearWindowConvolution r g Q (n + L + i)‖) / Q ≤ _
  simp_rw [hpoint]
  rw [← mul_sum]
  calc
    _ ≤ ((L : ℝ) / Q) * (∑ i ∈ range L, v i) / Q :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsub (by positivity)) hQr.le
    _ = ((L : ℝ) / Q) ^ 2 * ((∑ i ∈ range L, v i) / L) := by field_simp
    _ ≤ 9 * (16 * windowFourierNorm r n (6 * H)) := by
      apply mul_le_mul _ hlocal (by positivity) (by norm_num)
      have hnonneg : 0 ≤ (L : ℝ) / Q := by positivity
      nlinarith
    _ = _ := by ring

end Erdos335.IntermediateScale
