import Erdos335.PopularWindowEstimate
import Erdos335.DensityLimits

/-!
# Changing the averaging length of a prefix convolution
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Pointwise BigOperators

namespace Erdos335.IntermediateScale

theorem prefixConvolutionCount_mono (A B : Set ℕ) (x : ℕ) {H q : ℕ} (hHq : H ≤ q) :
    prefixConvolutionCount A B x H ≤ prefixConvolutionCount A B x q := by
  classical
  unfold prefixConvolutionCount
  exact card_le_card (filter_subset_filter _ (range_mono hHq))

theorem prefixConvolutionCount_length_bound (A B : Set ℕ) (x : ℕ)
    {H q : ℕ} (hHq : H ≤ q) :
    prefixConvolutionCount A B x q ≤ prefixConvolutionCount A B x H + (q - H) := by
  let P : Set ℕ := {b | b ∈ B ∧ b ≤ x ∧ x - b ∈ A}
  have heq (L : ℕ) : prefixConvolutionCount A B x L = Erdos335.prefixCount P L := by
    unfold prefixConvolutionCount Erdos335.prefixCount
    apply congrArg Finset.card
    ext b
    simp [P]
  rw [heq, heq]
  have hsplit := Erdos335.prefixCount_add_tailShift P H (q - H)
  rw [Nat.add_sub_of_le hHq] at hsplit
  have hbound := Erdos335.prefixCount_le (Erdos335.tailShift P H) (q - H)
  omega

theorem prefixConvolutionCount_abs_length_bound (A B : Set ℕ) (x : ℕ)
    {H q : ℕ} (hHq : H ≤ q) :
    |(prefixConvolutionCount A B x q : ℝ) - prefixConvolutionCount A B x H| ≤ (q - H : ℕ) := by
  have hm : (prefixConvolutionCount A B x H : ℝ) ≤ prefixConvolutionCount A B x q := by
    exact_mod_cast prefixConvolutionCount_mono A B x hHq
  have hb : (prefixConvolutionCount A B x q : ℝ) ≤
      prefixConvolutionCount A B x H + (q - H : ℕ) := by
    exact_mod_cast prefixConvolutionCount_length_bound A B x hHq
  rw [abs_of_nonneg (sub_nonneg.mpr hm)]
  linarith

noncomputable def convolutionTranslationErrorWithLength
    (A B : Set ℕ) (start q H : ℕ) [NeZero q] : ℝ :=
  ∑ c : ZMod q, |(prefixConvolutionCount A B (start + q + c.val) H : ℝ) -
    prefixConvolutionCount A B (start + c.val) H|

theorem convolutionTranslationError_length_bound
    (A B : Set ℕ) (start q H : ℕ) [NeZero q] (hHq : H ≤ q) :
    convolutionTranslationError A B start q ≤
      convolutionTranslationErrorWithLength A B start q H + 2 * q * (q - H : ℕ) := by
  have hpoint (c : ZMod q) :
      |(prefixConvolutionCount A B (start + q + c.val) q : ℝ) -
        prefixConvolutionCount A B (start + c.val) q| ≤
      |(prefixConvolutionCount A B (start + q + c.val) H : ℝ) -
        prefixConvolutionCount A B (start + c.val) H| + 2 * (q - H : ℕ) := by
    have hleft := prefixConvolutionCount_abs_length_bound A B (start + q + c.val) hHq
    have hright := prefixConvolutionCount_abs_length_bound A B (start + c.val) hHq
    have hfirst := abs_sub_le (prefixConvolutionCount A B (start + q + c.val) q : ℝ)
      (prefixConvolutionCount A B (start + q + c.val) H : ℝ)
      (prefixConvolutionCount A B (start + c.val) q : ℝ)
    have hsecond := abs_sub_le (prefixConvolutionCount A B (start + q + c.val) H : ℝ)
      (prefixConvolutionCount A B (start + c.val) H : ℝ)
      (prefixConvolutionCount A B (start + c.val) q : ℝ)
    rw [abs_sub_comm (prefixConvolutionCount A B (start + c.val) H : ℝ)] at hsecond
    linarith
  unfold convolutionTranslationError convolutionTranslationErrorWithLength
  calc
    _ ≤ ∑ c : ZMod q,
        (|(prefixConvolutionCount A B (start + q + c.val) H : ℝ) -
          prefixConvolutionCount A B (start + c.val) H| + 2 * (q - H : ℕ)) :=
      sum_le_sum (fun c _ => hpoint c)
    _ = _ := by simp [sum_add_distrib, mul_left_comm, mul_comm]

end Erdos335.IntermediateScale
