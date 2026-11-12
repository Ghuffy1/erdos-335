import Erdos335.LinearConvolutionLimits
import Erdos335.ConvolutionTranslationBounds
import Erdos335.PopularWindowEstimate

/-!
# The exact counting interpretation of a window convolution
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefixConvolutionCount_linear (A B : Set ℕ) (Q x : ℕ) (hQx : Q ≤ x) :
    (prefixConvolutionCount A B x Q : ℂ) / (Q : ℂ) =
      linearWindowConvolution (A.indicator (fun _ => (1 : ℝ)))
        (B.indicator (fun _ => (1 : ℂ))) Q x := by
  classical
  unfold linearWindowConvolution
  congr 1
  have hsum : (prefixConvolutionCount A B x Q : ℂ) =
      ∑ m ∈ range Q, if m ∈ B ∧ m ≤ x ∧ x - m ∈ A then (1 : ℂ) else 0 := by
    simp only [prefixConvolutionCount, card_eq_sum_ones, Nat.cast_sum, sum_filter]
    apply sum_congr rfl
    intro m hm
    split_ifs <;> norm_num
  rw [hsum]
  apply sum_congr rfl
  intro m hm
  have hmx : m ≤ x := (mem_range.mp hm).le.trans hQx
  by_cases hA : x - m ∈ A <;> by_cases hB : m ∈ B <;>
    simp [hA, hB, hmx]

theorem convolutionTranslationError_eq_linear (A B : Set ℕ) (Q start : ℕ) [NeZero Q]
    (hstart : Q ≤ start) :
    convolutionTranslationError A B start Q / (Q : ℝ) ^ 2 =
      linearConvolutionPeriodError (A.indicator (fun _ => (1 : ℝ)))
        (B.indicator (fun _ => (1 : ℂ))) Q start := by
  classical
  have hQr : (0 : ℝ) < Q := by exact_mod_cast NeZero.pos Q
  have hpoint (i : ℕ) (hi : i < Q) :
      ‖linearWindowConvolution (A.indicator (fun _ => (1 : ℝ)))
          (B.indicator (fun _ => (1 : ℂ))) Q (start + Q + i) -
        linearWindowConvolution (A.indicator (fun _ => (1 : ℝ)))
          (B.indicator (fun _ => (1 : ℂ))) Q (start + i)‖ =
      |(prefixConvolutionCount A B (start + Q + i) Q : ℝ) -
        prefixConvolutionCount A B (start + i) Q| / Q := by
    rw [← prefixConvolutionCount_linear A B Q (start + Q + i) (by omega),
      ← prefixConvolutionCount_linear A B Q (start + i) (by omega), ← sub_div,
      norm_div, Complex.norm_natCast]
    congr 1
    have heq : (prefixConvolutionCount A B (start + Q + i) Q : ℂ) -
        prefixConvolutionCount A B (start + i) Q =
        (((prefixConvolutionCount A B (start + Q + i) Q : ℝ) -
          prefixConvolutionCount A B (start + i) Q : ℝ) : ℂ) := by push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
  unfold convolutionTranslationError linearConvolutionPeriodError
  rw [sum_zmod_eq_range_real]
  have hsum : (∑ i ∈ range Q,
      ‖linearWindowConvolution (A.indicator (fun _ => (1 : ℝ)))
          (B.indicator (fun _ => (1 : ℂ))) Q (start + Q + i) -
        linearWindowConvolution (A.indicator (fun _ => (1 : ℝ)))
          (B.indicator (fun _ => (1 : ℂ))) Q (start + i)‖) =
      (∑ i ∈ range Q, |(prefixConvolutionCount A B (start + Q + i) Q : ℝ) -
        prefixConvolutionCount A B (start + i) Q|) / Q := by
    rw [sum_div]
    exact sum_congr rfl fun i hi => hpoint i (mem_range.mp hi)
  rw [hsum]
  have hvalues : (∑ i ∈ range Q,
      |(prefixConvolutionCount A B (start + Q + (i : ZMod Q).val) Q : ℝ) -
        prefixConvolutionCount A B (start + (i : ZMod Q).val) Q|) =
      ∑ i ∈ range Q, |(prefixConvolutionCount A B (start + Q + i) Q : ℝ) -
        prefixConvolutionCount A B (start + i) Q| := by
    exact sum_congr rfl fun i hi => by rw [ZMod.val_cast_of_lt (mem_range.mp hi)]
  rw [hvalues]
  ring

end Erdos335.IntermediateScale
