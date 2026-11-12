import Erdos335.WindowShiftAverages
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Recovering a prefix mean from averages of intermediate windows
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_sum_le_shifted_sum (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C) (N i : ℕ) :
    (∑ n ∈ range N, f n) ≤ (∑ n ∈ range N, f (n + i)) + C * i := by
  have hleft := sum_range_add f i N
  have hright := sum_range_add f N i
  rw [Nat.add_comm i N] at hleft
  have hnonneg : 0 ≤ ∑ n ∈ range i, f (N + n) := sum_nonneg fun n hn => (hf _).1
  have hhead : (∑ n ∈ range i, f n) ≤ C * i := by
    calc
      _ ≤ ∑ _n ∈ range i, C := sum_le_sum fun n hn => (hf n).2
      _ = _ := by simp; ring
  have heq : (∑ n ∈ range i, f n) + (∑ n ∈ range N, f (n + i)) =
      (∑ n ∈ range N, f n) + (∑ n ∈ range i, f (N + n)) := by
    simpa only [Nat.add_comm] using hleft.symm.trans hright
  linarith

theorem prefix_mean_le_offset_window_mean (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C) (N L W : ℕ) (hN : 0 < N) (hW : 0 < W) :
    (∑ n ∈ range N, f n) / N ≤
      (∑ n ∈ range N, (∑ i ∈ range W, f (n + L + i)) / W) / N +
        C * ((L + W : ℕ) : ℝ) / N := by
  have hC : 0 ≤ C := (hf 0).1.trans (hf 0).2
  have hdouble : (W : ℝ) * (∑ n ∈ range N, f n) ≤
      (∑ n ∈ range N, ∑ i ∈ range W, f (n + L + i)) +
        (W : ℝ) * (C * ((L + W : ℕ) : ℝ)) := by
    calc
      (W : ℝ) * (∑ n ∈ range N, f n) = ∑ _i ∈ range W, ∑ n ∈ range N, f n := by simp
      _ ≤ ∑ i ∈ range W, ((∑ n ∈ range N, f (n + L + i)) + C * ((L + W : ℕ) : ℝ)) := by
        apply sum_le_sum
        intro i hi
        have he := prefix_sum_le_shifted_sum f C hf N (L + i)
        have hbound : ((L + i : ℕ) : ℝ) ≤ ((L + W : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_le_add_left (mem_range.mp hi).le L
        have hle := add_le_add (le_refl (∑ n ∈ range N, f (n + (L + i))))
          (mul_le_mul_of_nonneg_left hbound hC)
        simpa only [Nat.add_assoc] using he.trans hle
      _ = _ := by rw [sum_add_distrib, sum_comm]; simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  rw [← sum_div]
  have hbound := div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right hdouble hWr.le) hNr.le
  convert hbound using 1 <;> field_simp

theorem prefix_mean_tendsto_zero_of_window_means
    (f : ℕ → ℝ) (C : ℝ) (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C)
    (N L W : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hW : ∀ s, 0 < W s)
    (hedge : Tendsto (fun s => (((L s + W s : ℕ) : ℝ)) / N s) atTop (𝓝 0))
    (hmean : Tendsto (fun s =>
      (∑ n ∈ range (N s), (∑ i ∈ range (W s), f (n + L s + i)) / W s) / N s) atTop (𝓝 0)) :
    Tendsto (fun s => (∑ n ∈ range (N s), f n) / N s) atTop (𝓝 0) := by
  apply squeeze_zero (fun s => div_nonneg (sum_nonneg fun n hn => (hf n).1) (by positivity))
    (fun s => prefix_mean_le_offset_window_mean f C hf (N s) (L s) (W s) (hN s) (hW s))
  have hedge' := hedge.const_mul C
  have hlim : Tendsto (fun s =>
      (∑ n ∈ range (N s), (∑ i ∈ range (W s), f (n + L s + i)) / W s) / N s +
        C * ((((L s + W s : ℕ) : ℝ)) / N s)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hmean.add hedge'
  exact hlim.congr (fun s => by ring)

end Erdos335.IntermediateScale
