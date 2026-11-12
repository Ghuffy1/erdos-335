import Erdos335.BlockFourierTransfer
import Erdos335.IntermediateCharacterMeans

/-!
# Exponential averages over an arbitrary integer interval
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem unitCharacter_nat_mul (β : ℝ) (n : ℕ) :
    unitCharacter ((n : ℝ) * β) = unitCharacter β ^ n := by
  induction n with
  | zero => simp [unitCharacter]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, unitCharacter_add, ih, pow_succ]

noncomputable def intervalCharacterMean (β : ℝ) (a L : ℕ) : ℂ :=
  (∑ n ∈ range L, unitCharacter (((a + n : ℕ) : ℝ) * β)) / (L : ℂ)

theorem intervalCharacterMean_norm_le (β : ℝ) (a L : ℕ)
    (hne : unitCharacter β ≠ 1) :
    ‖intervalCharacterMean β a L‖ ≤ 2 / ((L : ℝ) * ‖unitCharacter β - 1‖) := by
  let z := unitCharacter β
  have hz : ‖z‖ = 1 := unitCharacter_norm β
  have hdist : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hsum : (∑ n ∈ range L, unitCharacter (((a + n : ℕ) : ℝ) * β)) =
      unitCharacter ((a : ℝ) * β) * ∑ n ∈ range L, z ^ n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [Nat.cast_add, add_mul, unitCharacter_add, unitCharacter_nat_mul β n]
  have hnum : ‖z ^ L - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖z ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  rw [intervalCharacterMean, hsum, norm_div, norm_mul, unitCharacter_norm,
    one_mul, Complex.norm_natCast, geom_sum_eq hne, norm_div]
  calc
    _ ≤ (2 / ‖z - 1‖) / L :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum hdist.le) (Nat.cast_nonneg L)
    _ = _ := by ring

end Erdos335.IntermediateScale
