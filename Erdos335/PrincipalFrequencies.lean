import Erdos335.IntermediateFrequencySeparation
import Erdos335.BlockFourierTransfer
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Centered representatives of real frequencies modulo one
-/

set_option autoImplicit false

namespace Erdos335.IntermediateScale

noncomputable def principalFrequency (β : ℝ) : ℝ := β - (⌊β + 1 / 2⌋ : ℤ)

theorem principalFrequency_mem (β : ℝ) : principalFrequency β ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
  have hlo := Int.floor_le (β + 1 / 2)
  have hhi := Int.lt_floor_add_one (β + 1 / 2)
  constructor <;> dsimp [principalFrequency] <;> linarith

theorem unitCharacter_int (n : ℤ) : unitCharacter (n : ℝ) = 1 := by
  have heq : Complex.I * ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  unfold unitCharacter
  rw [heq]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem unitCharacter_principalFrequency (β : ℝ) : unitCharacter (principalFrequency β) = unitCharacter β := by
  have hz : unitCharacter (-((⌊β + 1 / 2⌋ : ℤ) : ℝ)) = 1 := by
    simpa only [Int.cast_neg] using unitCharacter_int (-⌊β + 1 / 2⌋)
  rw [principalFrequency, sub_eq_add_neg, unitCharacter_add, hz, mul_one]

noncomputable def circleFrequencyDistance (β : ℝ) : ℝ := |principalFrequency β|

theorem circleFrequencyDistance_mem (β : ℝ) : circleFrequencyDistance β ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  refine ⟨abs_nonneg _, ?_⟩
  apply abs_le.mpr
  constructor
  · linarith [(principalFrequency_mem β).1]
  · exact (principalFrequency_mem β).2

theorem circleFrequencyDistance_le_abs_sub_int (β : ℝ) (z : ℤ) :
    circleFrequencyDistance β ≤ |β - z| := by
  let k : ℤ := ⌊β + 1 / 2⌋
  by_cases hk : k = z
  · change |β - (k : ℝ)| ≤ |β - (z : ℝ)|
    rw [hk]
  · have hi : (1 : ℤ) ≤ |k - z| := by
      have hp : (0 : ℤ) < |k - z| := abs_pos.mpr (sub_ne_zero.mpr hk)
      omega
    have hr : (1 : ℝ) ≤ |(k : ℝ) - z| := by exact_mod_cast hi
    have heq : (k : ℝ) - z = (β - z) - principalFrequency β := by
      dsimp [principalFrequency, k]
      ring
    have ht := norm_sub_le (β - z) (principalFrequency β)
    simp only [Real.norm_eq_abs] at ht
    rw [← heq] at ht
    have hb := (circleFrequencyDistance_mem β).2
    change |principalFrequency β| ≤ |β - z|
    change |principalFrequency β| ≤ 1 / 2 at hb
    linarith

end Erdos335.IntermediateScale
