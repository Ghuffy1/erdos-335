import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Zero-density cut points for indicator primitives
-/

set_option autoImplicit false

open Set Filter MeasureTheory

namespace Erdos335.Loeb

theorem exists_zero_derivative_indicator_point
    (S J : Set ℝ) (hS : MeasurableSet S) (hpositive : 0 < volume (J \ S)) :
    ∃ c ∈ J \ S,
      HasDerivAt (fun y => ∫ x in 0..y, S.indicator (fun _ => (1 : ℝ)) x) 0 c := by
  let f : ℝ → ℝ := S.indicator fun _ => 1
  let F : ℝ → ℝ := fun y => ∫ x in 0..y, f x
  have hf : LocallyIntegrable f volume := (locallyIntegrable_const (1 : ℝ)).indicator hS
  let E : Set ℝ := {x | HasDerivAt F (f x) x}
  have hE : ∀ᵐ x : ℝ, x ∈ E := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf] with x hx
    exact hx 0
  have heq : (J \ S) ∩ E =ᵐ[volume] J \ S := by
    filter_upwards [hE] with x hx
    simp only [mem_inter_iff, hx, and_true]
  have hpos : 0 < volume ((J \ S) ∩ E) := by rwa [measure_congr heq]
  obtain ⟨c, hc, hderiv⟩ := nonempty_of_measure_ne_zero hpos.ne'
  refine ⟨c, hc, ?_⟩
  change HasDerivAt F (f c) c at hderiv
  simpa only [f, indicator_of_notMem hc.2] using hderiv

end Erdos335.Loeb
