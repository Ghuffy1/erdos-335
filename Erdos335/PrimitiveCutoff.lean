import Erdos335.IntervalTranslationLimits

/-!
# Constant continuation of a primitive at a zero derivative
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory

namespace Erdos335.Loeb

theorem hasDerivAt_left_constant_extension
    (F : ℝ → ℝ) (c : ℝ) (hF : HasDerivAt F 0 c) :
    HasDerivAt (fun x => if x ≤ c then F x else F c) 0 c := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h := hF.tendsto_slope.if' (p := fun y : ℝ => y ≤ c) tendsto_const_nhds
  convert h using 1
  funext y
  by_cases hy : y ≤ c <;> simp [slope, hy]

theorem primitive_upper_cutoff
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (c : ℝ) (hc : 0 ≤ c) (x : ℝ) :
    (∫ y in 0..x, (Iic c).indicator f y) =
      if x ≤ c then (∫ y in 0..x, f y) else (∫ y in 0..c, f y) := by
  have hg : LocallyIntegrable ((Iic c).indicator f) volume := hf.indicator measurableSet_Iic
  have hi (a b : ℝ) : IntervalIntegrable ((Iic c).indicator f) volume a b :=
    intervalIntegrable_iff.mpr ((hg.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hleft (z : ℝ) (hz : z ≤ c) :
      (∫ y in 0..z, (Iic c).indicator f y) = ∫ y in 0..z, f y := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with y
    intro hy
    have hyc : y ≤ c := (uIoc_subset_uIcc hy).2.trans (max_le hc hz)
    exact indicator_of_mem (show y ∈ Iic c from hyc) f
  by_cases hxc : x ≤ c
  · rw [if_pos hxc]
    exact hleft x hxc
  · rw [if_neg hxc, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c x), hleft c le_rfl]
    have hzero : (∫ y in c..x, (Iic c).indicator f y) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with y
      intro hy
      have hyc : c < y := by
        have hcx : c ≤ x := (not_le.mp hxc).le
        have hy' : y ∈ Ioc c x := by simpa only [uIoc_of_le hcx] using hy
        exact hy'.1
      exact indicator_of_notMem (show y ∉ Iic c from not_le.mpr hyc) f
    rw [hzero, add_zero]

theorem hasDerivAt_upper_cutoff_primitive
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (c : ℝ) (hc : 0 ≤ c)
    (hF : HasDerivAt (fun x => ∫ y in 0..x, f y) 0 c) :
    HasDerivAt (fun x => ∫ y in 0..x, (Iic c).indicator f y) 0 c := by
  have heq : (fun x => ∫ y in 0..x, (Iic c).indicator f y) =
      (fun x => if x ≤ c then (∫ y in 0..x, f y) else (∫ y in 0..c, f y)) :=
    funext (primitive_upper_cutoff f hf c hc)
  rw [heq]
  exact hasDerivAt_left_constant_extension _ c hF

end Erdos335.Loeb
