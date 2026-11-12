import Erdos335.LoebCounting
import Erdos335.LoebSaturation
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The counting Loeb probability measure

Countable saturation makes every countable internal cover of an internal
set reducible to a finite cover. The counting content is therefore sigma
subadditive. Mathlib's Carathéodory extension gives a measure agreeing with
the ultralimit of normalized counting on every internal set.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]

theorem internalCountingContent_sigmaSubadditive
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    (internalCountingContent (X := X) U).IsSigmaSubadditive := by
  intro f hf hUnion
  obtain ⟨m, hm⟩ := internal_countable_cover_has_finite U hU (⋃ k, f k) f
    hUnion hf (Set.Subset.refl _)
  let J := Finset.range (m + 1)
  have halg := isSetAlgebra_internalSets (X := X) U
  have hJ : (⋃ k ∈ J, f k) ∈ internalSets U := halg.biUnion_mem J (fun k _ => hf k)
  have hsub : (⋃ k, f k) ⊆ ⋃ k ∈ J, f k := by
    simpa only [J, Finset.mem_range, Nat.lt_succ_iff] using hm
  calc
    internalCountingContent U (⋃ k, f k) ≤ internalCountingContent U (⋃ k ∈ J, f k) :=
      addContent_mono halg.isSetRing.isSetSemiring hUnion hJ hsub
    _ ≤ ∑ k ∈ J, internalCountingContent U (f k) :=
      addContent_biUnion_le halg.isSetRing (fun k _ => hf k)
    _ ≤ ∑' k, internalCountingContent U (f k) := ENNReal.sum_le_tsum J

noncomputable abbrev loebMeasurableSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) :=
  (inducedOuterMeasure (fun S _ => internalCountingContent U S)
    (isSetAlgebra_internalSets (X := X) U).empty_mem addContent_empty).caratheodory

noncomputable def loebMeasure (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    @Measure ((U : Filter ℕ).Product X) (loebMeasurableSpace U) :=
  (internalCountingContent U).measureCaratheodory
    (isSetAlgebra_internalSets (X := X) U).isSetRing.isSetSemiring
    (internalCountingContent_sigmaSubadditive U hU)

theorem loebMeasure_internal (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ∀ n, Set (X n)) : loebMeasure U hU (internalSet U A) = ultraCount U A := by
  exact (AddContent.measureCaratheodory_eq (internalCountingContent U)
    (isSetAlgebra_internalSets (X := X) U).isSetRing.isSetSemiring
    (internalCountingContent_sigmaSubadditive U hU) ⟨A, rfl⟩).trans
      (internalCountingContent_internal U A)

theorem loebMeasure_univ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    loebMeasure (X := X) U hU univ = 1 := by
  rw [← internalSet_univ (X := X) U, loebMeasure_internal, ultraCount_univ]

theorem measurable_internalSet (U : Ultrafilter ℕ) (A : ∀ n, Set (X n)) :
    MeasurableSet[loebMeasurableSpace U] (internalSet U A) := by
  exact AddContent.isCaratheodory_inducedOuterMeasure_of_mem
    (isSetAlgebra_internalSets (X := X) U).isSetRing.isSetSemiring
    (internalCountingContent U) ⟨A, rfl⟩

theorem isProbabilityMeasure_loebMeasure (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) :
    @IsProbabilityMeasure ((U : Filter ℕ).Product X) (loebMeasurableSpace U)
      (loebMeasure U hU) where
  measure_univ := loebMeasure_univ U hU

end Erdos335.Loeb
