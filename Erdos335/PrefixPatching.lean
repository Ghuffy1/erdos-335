import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Prefix energy bounds for replacing an initial segment
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_patching_energy_bound (g h v : ℕ → ℝ) (N L : ℕ)
    (hg : ∀ n, g n ∈ Set.Icc (0 : ℝ) 1) (hh : ∀ n, h n ∈ Set.Icc (0 : ℝ) 1)
    (heq : ∀ n, L ≤ n → n < N → g n = v n) :
    ∑ n ∈ range N, (g n - h n) ^ 2 ≤ (L : ℝ) + ∑ n ∈ range N, (v n - h n) ^ 2 := by
  classical
  have hpoint (n : ℕ) (hn : n ∈ range N) : (g n - h n) ^ 2 ≤
      (if n < L then (1 : ℝ) else 0) + (v n - h n) ^ 2 := by
    by_cases hsmall : n < L
    · simp only [hsmall, ite_true]
      have hg' := hg n
      have hh' := hh n
      have hminus : 0 ≤ 1 - (g n - h n) := by linarith [hg'.2, hh'.1]
      have hplus : 0 ≤ 1 + (g n - h n) := by linarith [hg'.1, hh'.2]
      nlinarith [sq_nonneg (v n - h n), mul_nonneg hminus hplus]
    · simp only [hsmall, ite_false]
      rw [heq n (by omega) (mem_range.mp hn), zero_add]
  have hcard : ((range N).filter (fun n => n < L)).card ≤ L := by
    calc
      _ ≤ (range L).card := card_le_card (fun n hn => mem_range.mpr (mem_filter.mp hn).2)
      _ = _ := card_range L
  calc
    _ ≤ ∑ n ∈ range N, ((if n < L then (1 : ℝ) else 0) + (v n - h n) ^ 2) :=
      sum_le_sum hpoint
    _ = (((range N).filter (fun n => n < L)).card : ℝ) + ∑ n ∈ range N, (v n - h n) ^ 2 := by
      rw [sum_add_distrib, sum_boole]
    _ ≤ _ := add_le_add (by exact_mod_cast hcard) le_rfl

end Erdos335.IntermediateScale
