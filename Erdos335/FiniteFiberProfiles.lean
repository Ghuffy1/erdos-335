import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.AEDisjoint

/-!
# A set determined by full or empty finite fibers
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace Erdos335

theorem ae_eq_finite_preimage_of_fiber_measures
    {G F : Type*} [MeasurableSpace G] [Fintype F] [DecidableEq F]
    (μ : Measure G) [IsFiniteMeasure μ] (φ : G → F) (S : Set G) (hS : MeasurableSet S)
    (R : Finset F)
    (hprofile : ∀ r, μ (S ∩ φ ⁻¹' {r}) = if r ∈ R then μ (φ ⁻¹' {r}) else 0) :
    S =ᵐ[μ] φ ⁻¹' (R : Set F) := by
  classical
  let L : F → Set G := fun r => if r ∈ R then ∅ else S ∩ φ ⁻¹' {r}
  let T : F → Set G := fun r => if r ∈ R then (φ ⁻¹' {r}) \ S else ∅
  have hL (r : F) : μ (L r) = 0 := by
    by_cases hr : r ∈ R
    · simp only [L, if_pos hr, measure_empty]
    · simpa only [L, if_neg hr] using hprofile r
  have hT (r : F) : μ (T r) = 0 := by
    by_cases hr : r ∈ R
    · have hmass := measure_sdiff_add_inter (μ := μ) (φ ⁻¹' {r}) hS
      rw [inter_comm, hprofile r, if_pos hr] at hmass
      dsimp only [T]
      rw [if_pos hr]
      apply (ENNReal.add_left_inj (measure_ne_top μ (φ ⁻¹' {r}))).mp
      simpa only [zero_add] using hmass
    · simp only [T, if_neg hr, measure_empty]
  have hleft : μ (S \ φ ⁻¹' (R : Set F)) = 0 := by
    apply measure_mono_null ?_ (measure_iUnion_null hL)
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨φ x, ?_⟩
    have hn : φ x ∉ R := hx.2
    simpa only [L, if_neg hn, mem_inter_iff, mem_preimage, mem_singleton_iff, and_true] using hx.1
  have hright : μ ((φ ⁻¹' (R : Set F)) \ S) = 0 := by
    apply measure_mono_null ?_ (measure_iUnion_null hT)
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨φ x, ?_⟩
    have hr : φ x ∈ R := hx.1
    simpa only [T, if_pos hr, mem_sdiff, mem_preimage, mem_singleton_iff, true_and] using hx.2
  exact (ae_le_set.mpr hleft).antisymm (ae_le_set.mpr hright)

end Erdos335
