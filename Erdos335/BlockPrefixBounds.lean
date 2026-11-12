import Erdos335.BlockFourierWindows
import Mathlib.Tactic.FieldSimp

/-!
# Prefix estimates from complete-block estimates
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_zero_block_norm (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (H N : ℕ) (hH : 0 < H)
    (hzero : ∀ b, ∑ i ∈ range H, f (H * b + i) = 0) :
    ‖∑ i ∈ range N, f i‖ ≤ H := by
  have hfull := sum_full_blocks_eq_zero f H (N / H) (fun b hb => hzero b)
  simpa only [hfull, sub_zero] using prefix_block_remainder_norm f hf H N hH

theorem prefix_sum_le_of_block_bounds (v : ℕ → ℝ) (H N : ℕ) (hH : 0 < H)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hv : ∀ n, v n ≤ C)
    (hblock : ∀ b, ∑ i ∈ range H, v (H * b + i) ≤ A * H) :
    ∑ n ∈ range N, v n ≤ A * N + C * H := by
  have hdecomp : H * (N / H) + N % H = N := by
    have h := Nat.mod_add_div N H
    omega
  have hsum : (∑ n ∈ range N, v n) = (∑ n ∈ range (H * (N / H)), v n) +
      ∑ i ∈ range (N % H), v (H * (N / H) + i) := by
    simpa only [hdecomp] using sum_range_add v (H * (N / H)) (N % H)
  have hfull := sum_full_blocks_le v H (N / H) A (fun b hb => hblock b)
  have hlength : ((H * (N / H) : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.mul_div_le N H
  have hmain : (∑ n ∈ range (H * (N / H)), v n) ≤ A * N :=
    hfull.trans (mul_le_mul_of_nonneg_left hlength hA)
  have htail : (∑ i ∈ range (N % H), v (H * (N / H) + i)) ≤ C * H := by
    calc
      _ ≤ ∑ _i ∈ range (N % H), C := sum_le_sum fun i hi => hv _
      _ = C * (N % H : ℕ) := by simp [mul_comm]
      _ ≤ C * H := mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt N hH).le) hC
  rw [hsum]
  exact add_le_add hmain htail

theorem prefix_average_le_of_block_bounds (v : ℕ → ℝ) (H N : ℕ) (hH : 0 < H) (hN : 0 < N)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hv : ∀ n, v n ≤ C)
    (hblock : ∀ b, ∑ i ∈ range H, v (H * b + i) ≤ A * H) :
    (∑ n ∈ range N, v n) / N ≤ A + C * H / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbound := prefix_sum_le_of_block_bounds v H N hH A C hA hC hv hblock
  apply (div_le_iff₀ hNr).mpr
  have heq : (A + C * H / N) * N = A * N + C * H := by field_simp
  rw [heq]
  exact hbound

end Erdos335.IntermediateScale
