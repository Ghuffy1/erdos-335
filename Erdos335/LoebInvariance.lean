import Erdos335.LoebMaps

/-!
# Loeb invariance under internal bijections

Preservation of the internal counting content gives preservation of the
induced outer measure and measurability on its Carathéodory sigma algebra.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]

theorem loebOuterMeasure_map_equiv
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (e : ∀ n, X n ≃ X n) :
    OuterMeasure.map (productEquiv (U : Filter ℕ) e)
        (@Measure.toOuterMeasure ((U : Filter ℕ).Product X) (loebMeasurableSpace U)
          (loebMeasure U hU)) =
      @Measure.toOuterMeasure ((U : Filter ℕ).Product X) (loebMeasurableSpace U)
        (loebMeasure U hU) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let m : ∀ S : Set ((U : Filter ℕ).Product X), S ∈ internalSets U → ℝ≥0∞ :=
    fun S _ => internalCountingContent U S
  have hfun : (fun S => extend m (productEquiv (U : Filter ℕ) e ⁻¹' S)) = extend m := by
    funext S
    apply extend_congr m (internalSets_preimage_equiv_iff U e S)
    intro hs ht
    exact internalMass_preimage_equiv U e S
  have hm0 : extend m ∅ = 0 :=
    extend_empty (isSetAlgebra_internalSets (X := X) U).empty_mem addContent_empty
  change OuterMeasure.map (productEquiv (U : Filter ℕ) e)
    (OuterMeasure.ofFunction (extend m) hm0) = OuterMeasure.ofFunction (extend m) hm0
  rw [OuterMeasure.map_ofFunction (productEquiv (U : Filter ℕ) e).injective]
  simp only [hfun]

theorem loebMeasure_preimage_equiv
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (e : ∀ n, X n ≃ X n)
    (S : Set ((U : Filter ℕ).Product X)) :
    loebMeasure U hU (productEquiv (U : Filter ℕ) e ⁻¹' S) = loebMeasure U hU S := by
  exact congrArg (fun μ : OuterMeasure ((U : Filter ℕ).Product X) => μ S)
    (loebOuterMeasure_map_equiv U hU e)

theorem measurable_productEquiv
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (e : ∀ n, X n ≃ X n) :
    @Measurable ((U : Filter ℕ).Product X) ((U : Filter ℕ).Product X)
      (loebMeasurableSpace U) (loebMeasurableSpace U)
      (productEquiv (U : Filter ℕ) e) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  intro S hS
  change ∀ T, loebMeasure U hU T = loebMeasure U hU (T ∩ S) +
    loebMeasure U hU (T \ S) at hS
  change ∀ T, loebMeasure U hU T =
    loebMeasure U hU (T ∩ (productEquiv (U : Filter ℕ) e ⁻¹' S)) +
    loebMeasure U hU (T \ (productEquiv (U : Filter ℕ) e ⁻¹' S))
  intro T
  let E := productEquiv (U : Filter ℕ) e
  have hT : E ⁻¹' (E '' T) = T := E.injective.preimage_image T
  calc
    loebMeasure U hU T = loebMeasure U hU (E '' T) := by
      rw [← loebMeasure_preimage_equiv U hU e (E '' T), hT]
    _ = loebMeasure U hU ((E '' T) ∩ S) + loebMeasure U hU ((E '' T) \ S) := hS _
    _ = loebMeasure U hU (E ⁻¹' ((E '' T) ∩ S)) +
        loebMeasure U hU (E ⁻¹' ((E '' T) \ S)) := by
      rw [loebMeasure_preimage_equiv, loebMeasure_preimage_equiv]
    _ = _ := by rw [preimage_inter, preimage_sdiff, hT]

end Erdos335.Loeb
