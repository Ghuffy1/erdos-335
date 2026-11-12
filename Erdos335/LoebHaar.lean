import Erdos335.LoebCompactHom
import Erdos335.LoebTranslation
import Mathlib.MeasureTheory.Group.Measure

/-!
# Haar measure on compact ultralimit factors

A surjective measurable homomorphism sends the counting Loeb probability
measure to the Haar probability measure on its compact target.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Finite (X n)]

theorem loebMeasure_map_add_left (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (t : (U : Filter ℕ).Product X) :
    @Measure.map ((U : Filter ℕ).Product X) ((U : Filter ℕ).Product X)
      (loebMeasurableSpace U) (loebMeasurableSpace U) (fun x => t + x)
      (loebMeasure U hU) = loebMeasure U hU := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_add_left U hU t) hS]
  exact loebMeasure_preimage_add_left U hU t S

theorem loebMeasure_map_hom_isAddLeftInvariant
    {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : (U : Filter ℕ).Product X →+ E)
    (hq : @Measurable _ _ (loebMeasurableSpace U) _ q)
    (hsurj : Function.Surjective q) :
    Measure.IsAddLeftInvariant
      (@Measure.map _ _ (loebMeasurableSpace U) _ q (loebMeasure U hU)) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  constructor
  intro t
  obtain ⟨x, rfl⟩ := hsurj t
  rw [Measure.map_map (measurable_const_add (q x)) hq]
  have hcomp : ((fun y => q x + y) ∘ q) = q ∘ (fun y => x + y) := by
    funext y
    exact (q.map_add x y).symm
  rw [hcomp, ← Measure.map_map hq (measurable_add_left U hU x), loebMeasure_map_add_left]

theorem loebMeasure_map_hom_isAddHaarMeasure
    {E : Type*} [AddCommGroup E] [TopologicalSpace E] [CompactSpace E]
    [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : (U : Filter ℕ).Product X →+ E)
    (hq : @Measurable _ _ (loebMeasurableSpace U) _ q)
    (hsurj : Function.Surjective q) :
    Measure.IsAddHaarMeasure
      (@Measure.map _ _ (loebMeasurableSpace U) _ q (loebMeasure U hU)) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  letI : IsProbabilityMeasure (loebMeasure (X := X) U hU) :=
    isProbabilityMeasure_loebMeasure U hU
  let μ := (loebMeasure U hU).map q
  letI : Measure.IsAddLeftInvariant μ := loebMeasure_map_hom_isAddLeftInvariant U hU q hq hsurj
  exact Measure.isAddHaarMeasure_of_isCompact_nonempty_interior μ Set.univ
    isCompact_univ (by simp) (by simp [μ]) (by simp [μ])

theorem loebMeasure_compact_factor_isAddHaarMeasure
    {E : Type*} [AddCommGroup E] [MetricSpace E] [CompactSpace E]
    [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, X n →+ E) :
    Measure.IsAddHaarMeasure
      (@Measure.map _ _ (loebMeasurableSpace U) _
        (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU)) := by
  letI : CompactSpace (ultralimitAddHom U f).range :=
    isCompact_iff_compactSpace.mp (isCompact_range_ultralimitAddHom U hU f)
  exact loebMeasure_map_hom_isAddHaarMeasure U hU
    (ultralimitAddHom U f).rangeRestrict (measurable_rangeRestrict_ultralimitAddHom U f)
    (ultralimitAddHom U f).rangeRestrict_surjective

end Erdos335.Loeb
