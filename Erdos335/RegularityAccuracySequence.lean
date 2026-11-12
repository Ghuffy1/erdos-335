import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Accuracy sequences compatible with a prescribed complexity function
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

noncomputable def regularityAccuracy (d : ℝ → ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => regularityAccuracy d k / (2 * ((d (regularityAccuracy d k) : ℝ) + 1))

theorem regularityAccuracy_pos (d : ℝ → ℕ) (k : ℕ) : 0 < regularityAccuracy d k := by
  induction k with
  | zero => simp [regularityAccuracy]
  | succ k hk =>
    rw [regularityAccuracy]
    exact div_pos hk (by positivity)

theorem regularityAccuracy_step_le (d : ℝ → ℕ) (k : ℕ) :
    regularityAccuracy d (k + 1) ≤ regularityAccuracy d k / 2 := by
  rw [regularityAccuracy]
  apply div_le_div_of_nonneg_left (regularityAccuracy_pos d k).le (by norm_num)
  have hd : (0 : ℝ) ≤ d (regularityAccuracy d k) := Nat.cast_nonneg _
  nlinarith

theorem regularityAccuracy_geometric_bound (d : ℝ → ℕ) (k : ℕ) :
    regularityAccuracy d k ≤ (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp [regularityAccuracy]
  | succ k hk =>
    calc
      _ ≤ regularityAccuracy d k / 2 := regularityAccuracy_step_le d k
      _ ≤ (1 / 2 : ℝ) ^ k / 2 := div_le_div_of_nonneg_right hk (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem regularityAccuracy_tendsto_zero (d : ℝ → ℕ) :
    Tendsto (regularityAccuracy d) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => (regularityAccuracy_pos d k).le)
    (regularityAccuracy_geometric_bound d)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem regularityAccuracy_complexity_bound (d : ℝ → ℕ) (k : ℕ) :
    (d (regularityAccuracy d k) : ℝ) * regularityAccuracy d (k + 1) ≤ regularityAccuracy d k := by
  have hpos := regularityAccuracy_pos d k
  have hd : (0 : ℝ) ≤ d (regularityAccuracy d k) := Nat.cast_nonneg _
  rw [regularityAccuracy]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (show (0 : ℝ) < 2 * ((d (regularityAccuracy d k) : ℝ) + 1) by positivity)).mpr
  nlinarith

end Erdos335.IntermediateScale
