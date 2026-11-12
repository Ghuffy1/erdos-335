import Erdos335.HaarOverlapPositivePart
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circle overlap loss on a real fundamental interval
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace Erdos335.Loeb

theorem unitCircle_overlap_loss_eq_interval_integral
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S) (t : ℝ) :
    (volume S).toReal - haarOverlap volume S (t : AddCircle (1 : ℝ)) =
      ∫ x in 0..1, max (S.indicator (fun _ => (1 : ℝ)) (x : AddCircle (1 : ℝ)) -
        S.indicator (fun _ => (1 : ℝ)) ((x + t : ℝ) : AddCircle (1 : ℝ))) 0 := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let g : AddCircle (1 : ℝ) → ℝ := fun x =>
    max (S.indicator (fun _ => 1) x - S.indicator (fun _ => 1) ((t : AddCircle (1 : ℝ)) + x)) 0
  have hi : Measurable (S.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hS
  have hg : Measurable g := (hi.sub (hi.comp (measurable_const.add measurable_id))).max measurable_const
  have hp := AddCircle.measurePreserving_mk (1 : ℝ) 0
  calc
    (volume S).toReal - haarOverlap volume S (t : AddCircle (1 : ℝ)) = ∫ x, g x :=
      haarOverlap_loss_eq_positive_part_integral volume S hS _
    _ = ∫ (x : ℝ), g (x : AddCircle (1 : ℝ)) ∂volume.restrict (Ioc 0 1) := by
      rw [← hp.map_eq]
      simpa only [zero_add] using integral_map_of_stronglyMeasurable hp.measurable hg.stronglyMeasurable
    _ = _ := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [g, AddCircle.coe_add, add_comm]

end Erdos335.Loeb
