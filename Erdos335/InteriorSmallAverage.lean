import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Selecting a small value away from the end of a long prefix
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_small_before_tail (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (N T : ℕ) (hN : 0 < N) (hT : 2 * T ≤ N) :
    ∃ n < N - T, f n ≤ 2 * ((∑ j ∈ range N, f j) / N) := by
  have hD : 0 < N - T := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let a := (∑ j ∈ range N, f j) / N
  have ha : 0 ≤ a := div_nonneg (sum_nonneg fun j hj => hf j) hNr.le
  have hsum : (∑ j ∈ range N, f j) = (N : ℝ) * a := by dsimp [a]; field_simp
  have hcount : (N : ℝ) ≤ 2 * (N - T : ℕ) := by exact_mod_cast (show N ≤ 2 * (N - T) by omega)
  have hle : (∑ j ∈ range (N - T), f j) ≤ ∑ _j ∈ range (N - T), 2 * a := by
    calc
      _ ≤ ∑ j ∈ range N, f j := sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
        (fun j hj hnot => hf j)
      _ = (N : ℝ) * a := hsum
      _ ≤ (2 * (N - T : ℕ)) * a := mul_le_mul_of_nonneg_right hcount ha
      _ = _ := by simp; ring
  obtain ⟨n, hn, hv⟩ := exists_le_of_sum_le (show (range (N - T)).Nonempty by exact ⟨0, by simp [hD]⟩) hle
  exact ⟨n, mem_range.mp hn, hv⟩

theorem exists_small_interior_positions (f : ℕ → ℕ → ℝ) (hf : ∀ s n, 0 ≤ f s n)
    (N T : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (hT : Tendsto (fun s => (T s : ℝ) / N s) atTop (𝓝 0))
    (hmean : Tendsto (fun s => (∑ n ∈ range (N s), f s n) / N s) atTop (𝓝 0)) :
    ∃ n : ℕ → ℕ, (∀ s, n s < N s) ∧
      (∀ᶠ s in atTop, n s + T s ≤ N s) ∧ Tendsto (fun s => f s (n s)) atTop (𝓝 0) := by
  classical
  have htail : ∀ᶠ s in atTop, 2 * T s ≤ N s := by
    filter_upwards [hT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with s hs
    have hNr : (0 : ℝ) < N s := by exact_mod_cast hN s
    have hr := (div_lt_iff₀ hNr).mp hs
    have hrr : (2 : ℝ) * T s ≤ N s := by linarith
    exact_mod_cast hrr
  let n : ℕ → ℕ := fun s => if h : 2 * T s ≤ N s then
    (exists_small_before_tail (f s) (hf s) (N s) (T s) (hN s) h).choose else 0
  have hn (s : ℕ) (hs : 2 * T s ≤ N s) :
      n s < N s - T s ∧ f s (n s) ≤ 2 * ((∑ j ∈ range (N s), f s j) / N s) := by
    simpa only [n, dif_pos hs] using
      (exists_small_before_tail (f s) (hf s) (N s) (T s) (hN s) hs).choose_spec
  refine ⟨n, ?_, ?_, ?_⟩
  · intro s
    by_cases hs : 2 * T s ≤ N s
    · exact (hn s hs).1.trans_le (Nat.sub_le _ _)
    · simpa only [n, dif_neg hs] using hN s
  · filter_upwards [htail] with s hs
    have h := (hn s hs).1
    omega
  · apply squeeze_zero' (Eventually.of_forall fun s => hf s (n s)) ?_
      (by simpa only [mul_zero] using hmean.const_mul 2)
    exact htail.mono fun s hs => (hn s hs).2

end Erdos335.IntermediateScale
