import Erdos335.CircleNormArg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# A measure-preserving centered lift of small circle sets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace Erdos335.Loeb

theorem volume_centered_circle_lift
    (B : Set (AddCircle (1 : ℝ))) (hB : MeasurableSet B) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' B ∩ Ioc (-(1 / 2 : ℝ)) (1 / 2)) = volume B := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hp := AddCircle.measurePreserving_mk (1 : ℝ) (-(1 / 2 : ℝ))
  have h := congrArg (fun ν : Measure (AddCircle (1 : ℝ)) => ν B) hp.map_eq
  rw [Measure.map_apply hp.measurable hB, Measure.restrict_apply (hB.preimage hp.measurable)] at h
  convert h using 1 <;> norm_num

theorem centered_circle_lift_in_small_interval
    (B : Set (AddCircle (1 : ℝ))) (ε : ℝ)
    (hB : B ⊆ Metric.ball 0 ε) :
    (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' B ∩ Ioc (-(1 / 2 : ℝ)) (1 / 2)) ⊆ Ioo (-ε) ε := by
  intro x hx
  have habs : |x| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith [hx.2.1, hx.2.2]
  have hnorm : ‖(x : AddCircle (1 : ℝ))‖ = |x| :=
    (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr habs
  have hsmall := hB hx.1
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, hnorm] at hsmall
  exact abs_lt.mp hsmall

end Erdos335.Loeb
