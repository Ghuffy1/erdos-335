import Erdos335.PopularWindowEstimate
import Erdos335.CyclicWindowLiteralLift
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# From approximate convolution periods to exhaustive cyclic windows

The hypothesis is the normalized mean error between a prefix convolution
and its translate by the chosen window length. The conclusion retains
every fixed element of the original prefix input.
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem exists_positive_vanishing_divisor (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hlim : Tendsto e atTop (𝓝 0)) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun n => e n / δ n) atTop (𝓝 0) := by
  let δ := fun n : ℕ => Real.sqrt (e n) + 1 / ((n : ℝ) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hsqrt : Tendsto (fun n => Real.sqrt (e n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  refine ⟨δ, hδpos, ?_, ?_⟩
  · simpa only [add_zero] using hsqrt.add tendsto_one_div_add_atTop_nhds_zero_nat
  · apply squeeze_zero (fun n => div_nonneg (he n) (hδpos n).le) _ hsqrt
    intro n
    apply (div_le_iff₀ (hδpos n)).mpr
    have hsq := Real.sq_sqrt (he n)
    have hnonneg : 0 ≤ Real.sqrt (e n) * (1 / ((n : ℝ) + 1)) := by positivity
    dsimp only [δ]
    nlinarith

theorem popular_window_estimate_of_convolution_periods (A B : Set ℕ) (q start : ℕ → ℕ)
    [∀ n, NeZero (q n)]
    (hperiod : Tendsto (fun n => convolutionTranslationError A B (start n) (q n) /
      (q n : ℝ) ^ 2) atTop (𝓝 0)) :
    ∃ δ η : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      Tendsto η atTop (𝓝 0) ∧ ∀ n,
      ((ArithmeticRemoval.popularSum (cyclicWindow A (start n) (q n))
        (cyclicWindow B 0 (q n)) (δ n) \ cyclicWindow (A + B) (start n) (q n)).card : ℝ)
          ≤ η n * q n := by
  let e := fun n => convolutionTranslationError A B (start n) (q n) / (q n : ℝ) ^ 2
  have he (n : ℕ) : 0 ≤ e n := div_nonneg
    (convolutionTranslationError_nonneg A B (start n) (q n)) (sq_nonneg _)
  obtain ⟨δ, hδpos, hδ, hdiv⟩ := exists_positive_vanishing_divisor e he hperiod
  refine ⟨δ, fun n => e n / δ n, hδpos, hδ, hdiv, ?_⟩
  intro n
  have hq : (q n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (q n)
  have hbound := popular_window_count_bound A B (start n) (q n) (δ n) (hδpos n)
  apply hbound.trans_eq
  dsimp only [e]
  field_simp

theorem cyclic_window_removal_of_convolution_periods (A B : Set ℕ) (q start : ℕ → ℕ)
    [∀ n, NeZero (q n)] (hq : Tendsto q atTop atTop)
    (hperiod : Tendsto (fun n => convolutionTranslationError A B (start n) (q n) /
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
        atTop (𝓝 0) := by
  obtain ⟨δ, η, hδpos, hδ, hη, hbound⟩ :=
    popular_window_estimate_of_convolution_periods A B q start hperiod
  exact cyclic_window_removal_with_exhaustion A B q start hq δ η hδ hη
    (Eventually.of_forall hbound)

end Erdos335.IntermediateScale
