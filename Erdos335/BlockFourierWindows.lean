import Erdos335.FiniteBlockSums
import Mathlib.Analysis.Complex.Basic

/-!
# From Fourier bounds on aligned blocks to bounds on arbitrary windows
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_block_remainder_norm (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (H N : ℕ) (hH : 0 < H) :
    ‖(∑ i ∈ range N, f i) - ∑ i ∈ range (H * (N / H)), f i‖ ≤ H := by
  have hN : H * (N / H) + N % H = N := by
    have hmod := Nat.mod_add_div N H
    omega
  have hsum : (∑ i ∈ range N, f i) = (∑ i ∈ range (H * (N / H)), f i) +
      ∑ i ∈ range (N % H), f (H * (N / H) + i) := by
    simpa only [hN] using sum_range_add f (H * (N / H)) (N % H)
  rw [hsum, add_sub_cancel_left]
  calc
    _ ≤ ∑ i ∈ range (N % H), ‖f (H * (N / H) + i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range (N % H), (1 : ℝ) := sum_le_sum fun i hi => hf _
    _ = (N % H : ℕ) := by simp
    _ ≤ H := by exact_mod_cast (Nat.mod_lt N hH).le

theorem aligned_blocks_norm_bound (f : ℕ → ℂ) (H k l : ℕ) (hkl : k ≤ l) (ε : ℝ)
    (hblock : ∀ b, ‖∑ i ∈ range H, f (H * b + i)‖ ≤ ε * H) :
    ‖(∑ i ∈ range (H * l), f i) - ∑ i ∈ range (H * k), f i‖ ≤
      ε * H * (l - k : ℕ) := by
  rw [sum_full_blocks, sum_full_blocks, ← sum_Ico_eq_sub _ hkl]
  calc
    _ ≤ ∑ b ∈ Ico k l, ‖∑ i ∈ range H, f (H * b + i)‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ Ico k l, ε * H := sum_le_sum fun b hb => hblock b
    _ = _ := by simp; ring

theorem window_norm_bound_of_blocks (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (H n W : ℕ) (hH : 0 < H) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hblock : ∀ b, ‖∑ i ∈ range H, f (H * b + i)‖ ≤ ε * H) :
    ‖∑ i ∈ range W, f (n + i)‖ ≤ ε * W + 3 * H := by
  let P := fun t => ∑ i ∈ range t, f i
  let a := P (n + W)
  let a₀ := P (H * ((n + W) / H))
  let b := P n
  let b₀ := P (H * (n / H))
  have hq : n / H ≤ (n + W) / H := Nat.div_le_div_right (Nat.le_add_right n W)
  have hend : ‖a - a₀‖ ≤ H := prefix_block_remainder_norm f hf H (n + W) hH
  have hstart : ‖b - b₀‖ ≤ H := prefix_block_remainder_norm f hf H n hH
  have hmiddle : ‖a₀ - b₀‖ ≤ ε * H * ((n + W) / H - n / H : ℕ) :=
    aligned_blocks_norm_bound f H (n / H) ((n + W) / H) hq ε hblock
  have hsum : (∑ i ∈ range W, f (n + i)) = (a - a₀) + (a₀ - b₀) - (b - b₀) := by
    have hsplit := sum_range_add f n W
    change a = b + ∑ i ∈ range W, f (n + i) at hsplit
    linear_combination -hsplit
  have hspan : H * ((n + W) / H - n / H) ≤ W + H := by
    have hleft := Nat.mod_add_div n H
    have hright := Nat.mod_add_div (n + W) H
    have hrem := Nat.mod_lt n hH
    rw [Nat.mul_sub_left_distrib]
    omega
  have hspanR : (H : ℝ) * (((n + W) / H - n / H : ℕ) : ℝ) ≤ W + H := by
    exact_mod_cast hspan
  have hscaled := mul_le_mul_of_nonneg_left hspanR hε0
  have hεH : ε * H ≤ (H : ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg _) hε1
  rw [hsum]
  calc
    _ ≤ ‖(a - a₀) + (a₀ - b₀)‖ + ‖b - b₀‖ := norm_sub_le _ _
    _ ≤ (‖a - a₀‖ + ‖a₀ - b₀‖) + ‖b - b₀‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ε * W + 3 * H := by nlinarith

end Erdos335.IntermediateScale
