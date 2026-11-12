import Erdos335.PrefixConvolutionLengths
import Erdos335.ConvolutionPeriodWindowRemoval

/-!
# Cyclic removal from convolution periods at a nearby smaller length
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem convolution_period_error_of_nearby_length (A B : Set ℕ)
    (q H start : ℕ → ℕ) [∀ n, NeZero (q n)]
    (hHq : ∀ n, H n ≤ q n)
    (hgap : Tendsto (fun n => ((q n - H n : ℕ) : ℝ) / q n) atTop (𝓝 0))
    (hperiod : Tendsto (fun n => convolutionTranslationErrorWithLength A B (start n) (q n) (H n) /
      (q n : ℝ) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => convolutionTranslationError A B (start n) (q n) /
      (q n : ℝ) ^ 2) atTop (𝓝 0) := by
  have hup : Tendsto (fun n =>
      convolutionTranslationErrorWithLength A B (start n) (q n) (H n) / (q n : ℝ) ^ 2 +
        2 * (((q n - H n : ℕ) : ℝ) / q n)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hperiod.add (hgap.const_mul 2)
  apply squeeze_zero (fun n => div_nonneg
    (convolutionTranslationError_nonneg A B (start n) (q n)) (sq_nonneg _)) _ hup
  intro n
  have hq : (q n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (q n)
  have hbound := div_le_div_of_nonneg_right
    (convolutionTranslationError_length_bound A B (start n) (q n) (H n) (hHq n))
    (sq_nonneg (q n : ℝ))
  apply hbound.trans_eq
  field_simp

theorem cyclic_window_removal_of_nearby_convolution_periods (A B : Set ℕ)
    (q H start : ℕ → ℕ) [∀ n, NeZero (q n)] (hq : Tendsto q atTop atTop)
    (hHq : ∀ n, H n ≤ q n)
    (hgap : Tendsto (fun n => ((q n - H n : ℕ) : ℝ) / q n) atTop (𝓝 0))
    (hperiod : Tendsto (fun n => convolutionTranslationErrorWithLength A B (start n) (q n) (H n) /
      (q n : ℝ) ^ 2) atTop (𝓝 0)) :
    ∃ A' B' : ∀ n, Finset (ZMod (q n)),
      (∀ n, A' n ⊆ cyclicWindow A (start n) (q n) ∧ B' n ⊆ cyclicWindow B 0 (q n)) ∧
      (∀ b ∈ B, ∀ᶠ n in atTop, (b : ZMod (q n)) ∈ B' n) ∧
      Tendsto (fun n => ((cyclicWindow A (start n) (q n) \ A' n).card : ℝ) / q n)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ((cyclicWindow B 0 (q n) \ B' n).card : ℝ) / q n)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        (((A' n + B' n) \ cyclicWindow (A + B) (start n) (q n)).card : ℝ) / q n)
        atTop (𝓝 0) :=
  cyclic_window_removal_of_convolution_periods A B q start hq
    (convolution_period_error_of_nearby_length A B q H start hHq hgap hperiod)

end Erdos335.IntermediateScale
