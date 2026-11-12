import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite fiber decompositions of measure
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos335

theorem sum_measure_inter_fibers {X F : Type*} [MeasurableSpace X] [Fintype F]
    (μ : Measure X) (S : Set X) (φ : X → F)
    (hφ : ∀ r, MeasurableSet (φ ⁻¹' {r})) :
    (∑ r, μ (S ∩ φ ⁻¹' {r})) = μ S := by
  classical
  calc
    (∑ r, μ (S ∩ φ ⁻¹' {r})) = ∑ r, (μ.restrict S) (φ ⁻¹' {r}) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Measure.restrict_apply (hφ r), inter_comm]
    _ = (μ.restrict S) (φ ⁻¹' (Finset.univ : Finset F)) :=
      sum_measure_preimage_singleton Finset.univ (fun r hr => hφ r)
    _ = μ S := by simp

theorem sum_real_measure_inter_fibers {X F : Type*} [MeasurableSpace X] [Fintype F]
    (μ : Measure X) [IsFiniteMeasure μ] (S : Set X) (φ : X → F)
    (hφ : ∀ r, MeasurableSet (φ ⁻¹' {r})) :
    (∑ r, (μ (S ∩ φ ⁻¹' {r})).toReal) = (μ S).toReal := by
  have h := congrArg ENNReal.toReal (sum_measure_inter_fibers μ S φ hφ)
  rwa [ENNReal.toReal_sum (fun r hr => measure_ne_top μ _)] at h

end Erdos335
