import Erdos335.CyclicConvolutionCounts

/-!
# Popular cyclic sums from approximate convolution periods
-/

set_option autoImplicit false

open Finset
open scoped Pointwise BigOperators

namespace Erdos335.IntermediateScale

noncomputable def convolutionTranslationError (A B : Set ℕ) (start q : ℕ) [NeZero q] : ℝ :=
  ∑ c : ZMod q, |(prefixConvolutionCount A B (start + q + c.val) q : ℝ) -
    prefixConvolutionCount A B (start + c.val) q|

theorem convolutionTranslationError_nonneg (A B : Set ℕ) (start q : ℕ) [NeZero q] :
    0 ≤ convolutionTranslationError A B start q :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem popular_window_mass_bound (A B : Set ℕ) (start q : ℕ) [NeZero q] (δ : ℝ) :
    δ * q * ((ArithmeticRemoval.popularSum (cyclicWindow A start q)
      (cyclicWindow B 0 q) δ \ cyclicWindow (A + B) start q).card : ℝ) ≤
      convolutionTranslationError A B start q := by
  classical
  let bad := ArithmeticRemoval.popularSum (cyclicWindow A start q)
    (cyclicWindow B 0 q) δ \ cyclicWindow (A + B) start q
  let error := fun c : ZMod q => |(prefixConvolutionCount A B (start + q + c.val) q : ℝ) -
    prefixConvolutionCount A B (start + c.val) q|
  have hpoint (c : ZMod q) (hc : c ∈ bad) : δ * q ≤ error c := by
    obtain ⟨hpop, hout⟩ := mem_sdiff.mp hc
    have hpop' : δ * q < (ArithmeticRemoval.representationCount
        (cyclicWindow A start q) (cyclicWindow B 0 q) c : ℝ) := by
      simpa only [ArithmeticRemoval.popularSum, mem_filter, mem_univ, true_and,
        ZMod.card] using hpop
    have hcount := wrapped_representation_count_le A B start q c hout
    have hczero : prefixConvolutionCount A B (start + c.val) q = 0 := by
      apply prefixConvolutionCount_eq_zero
      intro hmem
      exact hout (mem_filter.mpr ⟨mem_univ _, hmem⟩)
    dsimp only [error]
    rw [hczero, Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hpop'.le.trans (by exact_mod_cast hcount)
  calc
    _ = ∑ _c ∈ bad, δ * q := by simp [bad, mul_comm]
    _ ≤ ∑ c ∈ bad, error c := sum_le_sum hpoint
    _ ≤ ∑ c : ZMod q, error c := sum_le_univ_sum_of_nonneg (fun _ => abs_nonneg _)
    _ = _ := rfl

theorem popular_window_count_bound (A B : Set ℕ) (start q : ℕ) [NeZero q]
    (δ : ℝ) (hδ : 0 < δ) :
    ((ArithmeticRemoval.popularSum (cyclicWindow A start q)
      (cyclicWindow B 0 q) δ \ cyclicWindow (A + B) start q).card : ℝ) ≤
      convolutionTranslationError A B start q / (δ * q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  apply (le_div_iff₀ (mul_pos hδ hq)).mpr
  simpa only [mul_comm] using popular_window_mass_bound A B start q δ

end Erdos335.IntermediateScale
