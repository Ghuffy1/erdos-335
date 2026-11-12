import Erdos335.LoebInvariance

/-!
# Counting Loeb measure under coordinate equivalences
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

variable {X Y : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Finite (Y n)]
variable [∀ n, Nonempty (X n)] [∀ n, Nonempty (Y n)]

theorem loebOuterMeasure_map_coordinateEquiv
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (e : ∀ n, X n ≃ Y n) :
    OuterMeasure.map (productEquiv (U : Filter ℕ) e)
      (@Measure.toOuterMeasure ((U : Filter ℕ).Product X) (loebMeasurableSpace U) (loebMeasure U hU)) =
      @Measure.toOuterMeasure ((U : Filter ℕ).Product Y) (loebMeasurableSpace U) (loebMeasure U hU) := by
  let mX : ∀ S : Set ((U : Filter ℕ).Product X), S ∈ internalSets U → ℝ≥0∞ :=
    fun S _ => internalCountingContent U S
  let mY : ∀ S : Set ((U : Filter ℕ).Product Y), S ∈ internalSets U → ℝ≥0∞ :=
    fun S _ => internalCountingContent U S
  have hfun : (fun S => extend mX (productEquiv (U : Filter ℕ) e ⁻¹' S)) = extend mY := by
    funext S
    apply extend_congr mX (internalSets_preimage_equiv_iff U e S)
    intro hs ht
    exact internalMass_preimage_equiv U e S
  have hmX : extend mX ∅ = 0 :=
    extend_empty (isSetAlgebra_internalSets (X := X) U).empty_mem addContent_empty
  have hmY : extend mY ∅ = 0 :=
    extend_empty (isSetAlgebra_internalSets (X := Y) U).empty_mem addContent_empty
  change OuterMeasure.map (productEquiv (U : Filter ℕ) e)
    (OuterMeasure.ofFunction (extend mX) hmX) = OuterMeasure.ofFunction (extend mY) hmY
  rw [OuterMeasure.map_ofFunction (productEquiv (U : Filter ℕ) e).injective]
  simp only [hfun]

theorem loebMeasure_preimage_coordinateEquiv
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (e : ∀ n, X n ≃ Y n)
    (S : Set ((U : Filter ℕ).Product Y)) :
    loebMeasure U hU (productEquiv (U : Filter ℕ) e ⁻¹' S) = loebMeasure U hU S := by
  exact congrArg (fun μ : OuterMeasure ((U : Filter ℕ).Product Y) => μ S)
    (loebOuterMeasure_map_coordinateEquiv U hU e)

theorem measurable_coordinateEquiv
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (e : ∀ n, X n ≃ Y n) :
    @Measurable ((U : Filter ℕ).Product X) ((U : Filter ℕ).Product Y)
      (loebMeasurableSpace U) (loebMeasurableSpace U) (productEquiv (U : Filter ℕ) e) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let : MeasurableSpace ((U : Filter ℕ).Product Y) := loebMeasurableSpace U
  intro S hS
  change ∀ T, loebMeasure U hU T = loebMeasure U hU (T ∩ S) + loebMeasure U hU (T \ S) at hS
  change ∀ T, loebMeasure U hU T =
    loebMeasure U hU (T ∩ (productEquiv (U : Filter ℕ) e ⁻¹' S)) +
      loebMeasure U hU (T \ (productEquiv (U : Filter ℕ) e ⁻¹' S))
  intro T
  let E := productEquiv (U : Filter ℕ) e
  have hT : E ⁻¹' (E '' T) = T := E.injective.preimage_image T
  calc
    loebMeasure U hU T = loebMeasure U hU (E '' T) := by
      rw [← loebMeasure_preimage_coordinateEquiv U hU e (E '' T), hT]
    _ = loebMeasure U hU ((E '' T) ∩ S) + loebMeasure U hU ((E '' T) \ S) := hS _
    _ = loebMeasure U hU (E ⁻¹' ((E '' T) ∩ S)) +
        loebMeasure U hU (E ⁻¹' ((E '' T) \ S)) := by
      rw [loebMeasure_preimage_coordinateEquiv, loebMeasure_preimage_coordinateEquiv]
    _ = _ := by rw [preimage_inter, preimage_sdiff, hT]

end Erdos335.Loeb
