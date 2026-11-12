import Erdos335.IntervalTranslationLimits

/-!
# Disjoint interval contributions to the positive translation loss
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace Erdos335.Loeb

theorem two_interval_integrals_le_positive_part
    (g : ℝ → ℝ) (hg : ∀ a b : ℝ, IntervalIntegrable g volume a b)
    (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hd : d ≤ 1) :
    (∫ x in a..b, g x) + (∫ x in c..d, g x) ≤ ∫ x in 0..1, max (g x) 0 := by
  let p : ℝ → ℝ := fun x => max (g x) 0
  have hp (x y : ℝ) : IntervalIntegrable p volume x y :=
    ⟨(hg x y).1.pos_part, (hg x y).2.pos_part⟩
  have hpos (x : ℝ) : 0 ≤ p x := le_max_right _ _
  have habound : (∫ x in a..b, g x) ≤ ∫ x in a..b, p x :=
    intervalIntegral.integral_mono_on hab (hg a b) (hp a b) (fun x _ => le_max_left _ _)
  have hcdbound : (∫ x in c..d, g x) ≤ ∫ x in c..d, p x :=
    intervalIntegral.integral_mono_on hcd (hg c d) (hp c d) (fun x _ => le_max_left _ _)
  have hzeroA := intervalIntegral.integral_nonneg_of_forall (μ := volume) ha hpos
  have hgap := intervalIntegral.integral_nonneg_of_forall (μ := volume) hbc hpos
  have hlast := intervalIntegral.integral_nonneg_of_forall (μ := volume) hd hpos
  have hzeroB := intervalIntegral.integral_add_adjacent_intervals (hp 0 a) (hp a b)
  have hzeroC := intervalIntegral.integral_add_adjacent_intervals (hp 0 b) (hp b c)
  have hzeroD := intervalIntegral.integral_add_adjacent_intervals (hp 0 c) (hp c d)
  have hone := intervalIntegral.integral_add_adjacent_intervals (hp 0 d) (hp d 1)
  change _ ≤ ∫ x in 0..1, p x
  linarith

theorem two_interval_translation_integrals_le
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (a b c d t : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    (∫ x in a..b, f x - f (x + t)) + (∫ x in c..d, f x - f (x + t)) ≤
      ∫ x in 0..1, max (f x - f (x + t)) 0 := by
  have hi (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  apply two_interval_integrals_le_positive_part (fun x => f x - f (x + t))
    _ a b c d ha hab hbc hcd hd
  intro x y
  exact (hi x y).sub ((IntervalIntegrable.comp_add_right_iff
    (f := f) (a := x) (b := y) (c := t)).mpr (hi (x + t) (y + t)))

end Erdos335.Loeb
