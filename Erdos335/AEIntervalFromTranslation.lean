import Erdos335.IntervalPositivePart
import Erdos335.AEIntervalStructure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Interval structure from a sharp small-translation estimate
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory

namespace Erdos335.Loeb

theorem ae_interval_of_sharp_translation_bound
    (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioo 0 1) (hSpos : 0 < volume S)
    (hboundary : HasDerivAt (fun y => ∫ x in 0..y, S.indicator (fun _ => (1 : ℝ)) x) 0 1)
    (t m : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (htpos : ∀ n, 0 < t n)
    (hm : Tendsto m atTop (𝓝 1))
    (hloss : ∀ n, (∫ x in 0..1,
      max (S.indicator (fun _ => (1 : ℝ)) x -
        S.indicator (fun _ => (1 : ℝ)) (x + t n)) 0) ≤ m n * t n) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ S =ᵐ[volume] Ioo a b := by
  let f : ℝ → ℝ := S.indicator fun _ => 1
  let F : ℝ → ℝ := fun y => ∫ x in 0..y, f x
  have hf : LocallyIntegrable f volume := (locallyIntegrable_const (1 : ℝ)).indicator hSm
  let E : Set ℝ := {x | HasDerivAt F (f x) x}
  have hE : ∀ᵐ x : ℝ, x ∈ E := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf] with x hx
    exact hx 0
  apply ae_interval_of_order_convex_on_full_measure_set S E hS hE hSpos
  intro a ha b hb x hx hax hxb
  by_contra hxS
  have hda : HasDerivAt F 1 a := by
    have h := ha.2
    change HasDerivAt F (f a) a at h
    simpa only [f, indicator_of_mem ha.1] using h
  have hdx : HasDerivAt F 0 x := by
    change HasDerivAt F (f x) x at hx
    simpa only [f, indicator_of_notMem hxS] using hx
  have hdb : HasDerivAt F 1 b := by
    have h := hb.2
    change HasDerivAt F (f b) b at h
    simpa only [f, indicator_of_mem hb.1] using h
  have hbound : (1 : ℝ) - 0 + 1 - 0 ≤ 1 :=
    derivative_alternating_sum_le_of_varying_translation_integrals f hf a x b 1 1 0 1 0 1
      hda hdx hdb hboundary t ht htpos m hm (fun n =>
        (two_interval_translation_integrals_le f hf a x b 1 (t n)
          (hS ha.1).1.le hax.le hxb.le (hS hb.1).2.le le_rfl).trans (hloss n))
  norm_num at hbound

end Erdos335.Loeb
