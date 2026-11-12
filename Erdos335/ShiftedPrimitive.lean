import Erdos335.IntervalTranslationLimits
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Moving a zero-derivative point of an integral to the origin
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory

namespace Erdos335.Loeb

theorem shifted_primitive_derivative_zero
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (c : ℝ)
    (hderiv : HasDerivAt (fun y => ∫ x in 0..y, f x) 0 c) :
    HasDerivAt (fun y => ∫ x in 0..y, f (x + c)) 0 0 := by
  have hi (a b : ℝ) : IntervalIntegrable f volume a b :=
    intervalIntegrable_iff.mpr ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hformula (y : ℝ) : (∫ x in 0..y, f (x + c)) =
      (∫ x in 0..y + c, f x) - ∫ x in 0..c, f x := by
    rw [intervalIntegral.integral_comp_add_right, zero_add]
    exact (intervalIntegral.integral_interval_sub_left (hi 0 (y + c)) (hi 0 c)).symm
  have hshift : HasDerivAt (fun y => ∫ x in 0..y + c, f x) 0 0 :=
    HasDerivAt.comp_add_const 0 c (by simpa only [zero_add] using hderiv)
  have h := hshift.sub_const (∫ x in 0..c, f x)
  have heq : (fun y => (∫ x in 0..y + c, f x) - ∫ x in 0..c, f x) =
      (fun y => ∫ x in 0..y, f (x + c)) := funext fun y => (hformula y).symm
  rwa [heq] at h

end Erdos335.Loeb
