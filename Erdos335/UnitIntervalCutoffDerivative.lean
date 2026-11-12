import Erdos335.PrimitiveCutoff
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The derivative at the upper endpoint of a unit-interval cutoff
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory

namespace Erdos335.Loeb

theorem periodic_primitive_add_one
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hperiod : Function.Periodic f 1) (x : ℝ) :
    (∫ y in 0..x + 1, f y) = (∫ y in 0..x, f y) + ∫ y in 0..1, f y := by
  have hi (a b : ℝ) : IntervalIntegrable f volume a b :=
    intervalIntegrable_iff.mpr ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  simpa only [zero_add] using hperiod.intervalIntegral_add_eq_add 0 x hi

theorem periodic_primitive_derivative_zero_one
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hperiod : Function.Periodic f 1)
    (hzero : HasDerivAt (fun x => ∫ y in 0..x, f y) 0 0) :
    HasDerivAt (fun x => ∫ y in 0..x, f y) 0 1 := by
  let F : ℝ → ℝ := fun x => ∫ y in 0..x, f y
  have htranslate (x : ℝ) : F (x - 1) + F 1 = F x := by
    have h := periodic_primitive_add_one f hf hperiod (x - 1)
    simpa only [sub_add_cancel] using h.symm
  have hshift : HasDerivAt (fun x => F (x - 1)) 0 1 :=
    HasDerivAt.comp_sub_const 1 1 (by simpa only [sub_self] using hzero)
  have h := hshift.add_const (F 1)
  have heq : (fun x => F (x - 1) + F 1) = F := funext htranslate
  rw [heq] at h
  exact h

theorem unit_interval_cutoff_derivative_zero
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hone : f 1 = 0)
    (hF : HasDerivAt (fun x => ∫ y in 0..x, f y) 0 1) :
    HasDerivAt (fun x => ∫ y in 0..x, (Ioo (0 : ℝ) 1).indicator f y) 0 1 := by
  have hpoint (y : ℝ) (hy : 0 < y) :
      (Ioo (0 : ℝ) 1).indicator f y = (Iic (1 : ℝ)).indicator f y := by
    by_cases hy1 : y < 1
    · rw [indicator_of_mem (show y ∈ Ioo (0 : ℝ) 1 from ⟨hy, hy1⟩),
        indicator_of_mem (show y ∈ Iic (1 : ℝ) from hy1.le)]
    · by_cases heq : y = 1
      · subst y
        simp [hone]
      · have hygt : 1 < y := lt_of_le_of_ne (not_lt.mp hy1) (Ne.symm heq)
        rw [indicator_of_notMem (show y ∉ Ioo (0 : ℝ) 1 from fun h => hy1 h.2),
          indicator_of_notMem (show y ∉ Iic (1 : ℝ) from not_le.mpr hygt)]
  have hcut := hasDerivAt_upper_cutoff_primitive f hf 1 zero_le_one hF
  apply hcut.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 from zero_lt_one)] with x hx
  apply intervalIntegral.integral_congr_uIoo
  intro y hy
  have hypos : 0 < y := by
    have hy' : y ∈ Ioo (0 : ℝ) x := by simpa only [uIoo_of_le hx.le] using hy
    exact hy'.1
  exact hpoint y hypos

theorem periodic_unit_cutoff_derivative_zero
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hperiod : Function.Periodic f 1)
    (hfzero : f 0 = 0) (hzero : HasDerivAt (fun x => ∫ y in 0..x, f y) 0 0) :
    HasDerivAt (fun x => ∫ y in 0..x, (Ioo (0 : ℝ) 1).indicator f y) 0 1 := by
  have hone : f 1 = 0 := by simpa only [zero_add] using (hperiod 0).trans hfzero
  exact unit_interval_cutoff_derivative_zero f hf hone
    (periodic_primitive_derivative_zero_one f hf hperiod hzero)

end Erdos335.Loeb
