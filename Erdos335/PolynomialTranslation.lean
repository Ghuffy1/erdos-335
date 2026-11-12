import Erdos335.BlockFourierTransfer

/-!
# Translation estimates for a finite trigonometric polynomial
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem polynomial_translation_norm_le {d : ℕ} (c : Fin d → ℂ) (α : Fin d → ℝ)
    (n Q : ℕ) (η : ℝ) (hc : ∀ j, ‖c j‖ ≤ 1)
    (hphase : ∀ j, ‖unitCharacter ((Q : ℝ) * α j) - 1‖ ≤ η) :
    ‖(∑ j, c j * unitCharacter (((n + Q : ℕ) : ℝ) * α j)) -
      ∑ j, c j * unitCharacter ((n : ℝ) * α j)‖ ≤ d * η := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖c j * unitCharacter (((n + Q : ℕ) : ℝ) * α j) -
        c j * unitCharacter ((n : ℝ) * α j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, η := by
      apply sum_le_sum
      intro j hj
      have heq : c j * unitCharacter (((n + Q : ℕ) : ℝ) * α j) -
          c j * unitCharacter ((n : ℝ) * α j) =
          c j * unitCharacter ((n : ℝ) * α j) * (unitCharacter ((Q : ℝ) * α j) - 1) := by
        rw [Nat.cast_add, add_mul, unitCharacter_add]
        ring
      rw [heq, norm_mul, norm_mul, unitCharacter_norm, mul_one]
      calc
        _ ≤ 1 * ‖unitCharacter ((Q : ℝ) * α j) - 1‖ :=
          mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _)
        _ ≤ η := by simpa only [one_mul] using hphase j
    _ = _ := by simp

end Erdos335.IntermediateScale
