import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Quantitative decay for the compact inverse iteration

The e-transform recurrence from Griesmer's Lemma 6.1 forces the retained
summand's measure to tend to zero. The bound holds even if an iterate is
zero.
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.Loeb

theorem shrinking_measure_le_reciprocal
    (b : ℕ → ℝ) (hzero : ∀ n, 0 ≤ b n) (hinitial : b 0 ≤ 1)
    (hstep : ∀ n, b (n + 1) ≤ (1 - b n) * b n) :
    ∀ n, b n ≤ 1 / ((n : ℝ) + 1) := by
  intro n
  induction n with
  | zero => simpa using hinitial
  | succ n ih =>
    have hden : 0 < 1 + b n := by linarith [hzero n]
    have hdenN : 0 < (n : ℝ) + 1 := by positivity
    have hdenN' : 0 < (n : ℝ) + 2 := by positivity
    have hfirst : (1 - b n) * b n ≤ b n / (1 + b n) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith [sq_nonneg (b n), mul_nonneg (hzero n) (sq_nonneg (b n))]
    have hbn : b n * ((n : ℝ) + 1) ≤ 1 := (le_div_iff₀ hdenN).mp ih
    have hsecond : b n / (1 + b n) ≤ 1 / ((n : ℝ) + 2) := by
      apply (div_le_div_iff₀ hden hdenN').mpr
      nlinarith
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      (hstep n).trans (hfirst.trans hsecond)

theorem shrinking_measure_tendsto_zero
    (b : ℕ → ℝ) (hzero : ∀ n, 0 ≤ b n) (hinitial : b 0 ≤ 1)
    (hstep : ∀ n, b (n + 1) ≤ (1 - b n) * b n) :
    Tendsto b atTop (𝓝 0) := by
  exact squeeze_zero hzero (shrinking_measure_le_reciprocal b hzero hinitial hstep)
    tendsto_one_div_add_atTop_nhds_zero_nat

end Erdos335.Loeb
