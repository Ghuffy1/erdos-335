import Erdos335.WindowMeanTransfer

/-!
# Recovering prefix profiles from averaged offset windows

Privately checked supporting development.
The finite estimate combines the two canonical shifted-prefix inequalities.
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem offset_window_mean_le_prefix_mean
    (f : ℕ → ℝ) (C : ℝ) (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C)
    (N J H : ℕ) (hN : 0 < N) (hH : 0 < H) :
    (∑ n ∈ range N, (∑ i ∈ range H, f (n + J + i)) / H) / N ≤
      (∑ n ∈ range N, f n) / N + C * ((J + H : ℕ) : ℝ) / N := by
  have hC : 0 ≤ C := (hf 0).1.trans (hf 0).2
  have hdouble : (∑ n ∈ range N, ∑ i ∈ range H, f (n + J + i)) ≤
      (H : ℝ) * ((∑ n ∈ range N, f n) + C * ((J + H : ℕ) : ℝ)) := by
    rw [sum_comm]
    calc
      _ ≤ ∑ _i ∈ range H, ((∑ n ∈ range N, f n) + C * ((J + H : ℕ) : ℝ)) := by
        apply sum_le_sum
        intro i hi
        have hshift := shifted_prefix_sum_le f C hf N (J + i)
        have hindex : ((J + i : ℕ) : ℝ) ≤ ((J + H : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_le_add_left (mem_range.mp hi).le J
        have hbound := hshift.trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hindex hC))
        simpa only [Nat.add_assoc] using hbound
      _ = _ := by simp; ring
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  rw [← sum_div]
  calc
    _ ≤ ((H : ℝ) * ((∑ n ∈ range N, f n) + C * ((J + H : ℕ) : ℝ)) / H) / N :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hdouble hHr.le) hNr.le
    _ = _ := by field_simp

theorem abs_prefix_mean_sub_offset_window_mean_le
    (f : ℕ → ℝ) (C : ℝ) (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C)
    (N J H : ℕ) (hN : 0 < N) (hH : 0 < H) :
    |(∑ n ∈ range N, f n) / N -
      (∑ n ∈ range N, (∑ i ∈ range H, f (n + J + i)) / H) / N| ≤
        C * ((J + H : ℕ) : ℝ) / N := by
  have hforward := prefix_mean_le_offset_window_mean f C hf N J H hN hH
  have hreverse := offset_window_mean_le_prefix_mean f C hf N J H hN hH
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem prefix_mean_tendsto_of_offset_window_means
    (f : ℕ → ℝ) (C p : ℝ) (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C)
    (N J H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hH : ∀ s, 0 < H s)
    (hedge : Tendsto (fun s => ((J s + H s : ℕ) : ℝ) / N s) atTop (𝓝 0))
    (hmean : Tendsto (fun s =>
      (∑ n ∈ range (N s), (∑ i ∈ range (H s), f (n + J s + i)) / H s) / N s)
      atTop (𝓝 p)) :
    Tendsto (fun s => (∑ n ∈ range (N s), f n) / N s) atTop (𝓝 p) := by
  have herror : Tendsto (fun s =>
      |(∑ n ∈ range (N s), f n) / N s -
        (∑ n ∈ range (N s), (∑ i ∈ range (H s), f (n + J s + i)) / H s) / N s|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun s => abs_nonneg _)
      (fun s => abs_prefix_mean_sub_offset_window_mean_le f C hf (N s) (J s) (H s) (hN s) (hH s))
    simpa only [mul_zero, mul_div_assoc] using hedge.const_mul C
  have hdifference : Tendsto (fun s =>
      (∑ n ∈ range (N s), f n) / N s -
        (∑ n ∈ range (N s), (∑ i ∈ range (H s), f (n + J s + i)) / H s) / N s)
      atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using herror
  have hsum := hdifference.add hmean
  simpa only [sub_add_cancel, zero_add] using hsum

end Erdos335.IntermediateScale