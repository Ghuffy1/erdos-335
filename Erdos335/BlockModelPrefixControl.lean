import Erdos335.BlockPrefixBounds
import Erdos335.IntegerCircleCharacters
import Mathlib.Algebra.BigOperators.Fin

/-!
# Prefix mean and polynomial error control for block models
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_zero_block_real_average (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (H N : ℕ) (hH : 0 < H) (hzero : ∀ b, ∑ i ∈ range H, f (H * b + i) = 0) :
    |(∑ i ∈ range N, f i) / N| ≤ (H : ℝ) / N := by
  have hcomplex : ∀ b, ∑ i ∈ range H, (f (H * b + i) : ℂ) = 0 := by
    intro b
    exact_mod_cast hzero b
  have hbound := prefix_zero_block_norm (fun n => (f n : ℂ))
    (fun n => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf n) H N hH hcomplex
  have hreal : |∑ i ∈ range N, f i| ≤ (H : ℝ) := by
    simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using hbound
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [abs_div, abs_of_nonneg hN0]
  exact div_le_div_of_nonneg_right hreal hN0

theorem real_frequency_polynomial_norm_le {L : ℕ}
    (a : Fin L → ℂ) (α : Fin L → ℝ) (x : ℝ) (ha : ∀ j, ‖a j‖ ≤ 1) :
    ‖∑ j, a j * unitCharacter (x * α j)‖ ≤ L := by
  calc
    _ ≤ ∑ j, ‖a j * unitCharacter (x * α j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin L, (1 : ℝ) := by
      apply sum_le_sum
      intro j hj
      simpa only [norm_mul, unitCharacter_norm, mul_one] using ha j
    _ = _ := by simp

theorem prefix_polynomial_model_error (g : ℕ → ℝ) (P : ℕ → ℂ)
    (hg : ∀ n, g n ∈ Set.Icc (0 : ℝ) 1) (L : ℕ) (hP : ∀ n, ‖P n‖ ≤ L)
    (H N : ℕ) (hH : 0 < H) (hN : 0 < N) (ε : ℝ)
    (hblock : ∀ b, ∑ i ∈ range H, ‖(g (H * b + i) : ℂ) - P (H * b + i)‖ ^ 2 ≤ ε ^ 2 * H) :
    (∑ n ∈ range N, ‖(g n : ℂ) - P n‖ ^ 2) / N ≤
      ε ^ 2 + ((L : ℝ) + 1) ^ 2 * H / N := by
  apply prefix_average_le_of_block_bounds _ H N hH hN (ε ^ 2) (((L : ℝ) + 1) ^ 2)
    (sq_nonneg _) (sq_nonneg _) _ hblock
  intro n
  have hgNorm : ‖(g n : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg n).1] using (hg n).2
  have hbound := (norm_sub_le (g n : ℂ) (P n)).trans (add_le_add hgNorm (hP n))
  nlinarith [norm_nonneg ((g n : ℂ) - P n)]

end Erdos335.IntermediateScale
