import Erdos335.WindowFourierNorm

/-!
# Prefix bounds for averages of shifted nonnegative functions
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem shifted_prefix_sum_le (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C) (N i : ℕ) :
    (∑ n ∈ range N, f (n + i)) ≤ (∑ n ∈ range N, f n) + C * i := by
  have hleft := sum_range_add f i N
  have hright := sum_range_add f N i
  rw [Nat.add_comm i N] at hleft
  have hnonneg : 0 ≤ ∑ n ∈ range i, f n := sum_nonneg fun n hn => (hf n).1
  have htail : (∑ n ∈ range i, f (N + n)) ≤ C * i := by
    calc
      _ ≤ ∑ _n ∈ range i, C := sum_le_sum fun n hn => (hf _).2
      _ = _ := by simp; ring
  have heq : (∑ n ∈ range i, f n) + (∑ n ∈ range N, f (n + i)) =
      (∑ n ∈ range N, f n) + (∑ n ∈ range i, f (N + n)) := by
    simpa only [Nat.add_comm] using hleft.symm.trans hright
  linarith

theorem averaged_window_sum_le (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C) (N W : ℕ) (hN : 0 < N) (hW : 0 < W) :
    (∑ n ∈ range N, (∑ i ∈ range W, f (n + i)) / W) / N ≤
      (∑ n ∈ range N, f n) / N + C * (W : ℝ) / N := by
  have hC : 0 ≤ C := (hf 0).1.trans (hf 0).2
  have hdouble : (∑ n ∈ range N, ∑ i ∈ range W, f (n + i)) ≤
      W * ((∑ n ∈ range N, f n) + C * W) := by
    rw [sum_comm]
    calc
      _ ≤ ∑ _i ∈ range W, ((∑ n ∈ range N, f n) + C * W) := by
        apply sum_le_sum
        intro i hi
        exact (shifted_prefix_sum_le f C hf N i).trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_range.mp hi).le) hC))
      _ = _ := by simp; ring
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  rw [← sum_div]
  calc
    _ ≤ (W * ((∑ n ∈ range N, f n) + C * W) / W) / N :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hdouble hWr.le) hNr.le
    _ = _ := by field_simp

end Erdos335.IntermediateScale
