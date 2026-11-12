import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Prefix energy identities for asymptotically orthogonal decompositions
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

noncomputable def prefixEnergy (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, f n ^ 2) / N

noncomputable def prefixCorrelation (f g : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, f n * g n) / N

theorem prefixEnergy_nonneg (f : ℕ → ℝ) (N : ℕ) : 0 ≤ prefixEnergy f N :=
  div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem prefixEnergy_le_one (f : ℕ → ℝ) (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    prefixEnergy f N ≤ 1 := by
  have hsum : ∑ n ∈ range N, f n ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ range N, (1 : ℝ) := by
        apply sum_le_sum
        intro n hn
        nlinarith [(hf n).1, (hf n).2]
      _ = _ := by simp
  by_cases hN : N = 0
  · simp [prefixEnergy, hN]
  · have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    exact (div_le_one hNr).mpr hsum

theorem prefix_distance_energy_identity (F g h : ℕ → ℝ) (N : ℕ) :
    prefixEnergy (fun n => h n - g n) N = prefixEnergy h N - prefixEnergy g N +
      2 * prefixCorrelation g (fun n => F n - h n) N -
      2 * prefixCorrelation g (fun n => F n - g n) N := by
  have hpoint (n : ℕ) : (h n - g n) ^ 2 = h n ^ 2 - g n ^ 2 +
      2 * (g n * (F n - h n)) - 2 * (g n * (F n - g n)) := by ring
  unfold prefixEnergy prefixCorrelation
  simp_rw [hpoint, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  simp only [sum_sub_distrib]
  ring

end Erdos335.IntermediateScale
