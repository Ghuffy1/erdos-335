import Erdos335.LoebInnerMeasure

/-!
# Sets of full inner measure inside a measurable set

Completeness of Loeb measure turns full inner measure in a measurable
superset into measurability and almost-everywhere equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]

local instance fullInnerLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loebMeasure_sdiff_eq_zero_of_full_inner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S T : Set ((U : Filter ℕ).Product X)) (hST : S ⊆ T)
    (hfull : internalInnerMeasure U hU S = loebMeasure U hU T) :
    loebMeasure U hU (T \ S) = 0 := by
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let I := {A : Set ((U : Filter ℕ).Product X) // A ∈ internalSets U ∧ A ⊆ S}
  letI : Nonempty I := ⟨⟨∅, ⟨fun _ => ∅, internalSet_empty U⟩, empty_subset S⟩⟩
  have hbound : μ (T \ S) + internalInnerMeasure U hU S ≤ μ T := by
    unfold internalInnerMeasure
    rw [ENNReal.add_iSup]
    apply iSup_le
    intro A
    have hAm : MeasurableSet A.1 := by
      obtain ⟨V, hV⟩ := A.2.1
      rw [← hV]
      exact measurable_internalSet U V
    have hd : Disjoint (T \ S) A.1 := by
      apply Set.disjoint_left.mpr
      intro x hx hAx
      exact hx.2 (A.2.2 hAx)
    calc
      μ (T \ S) + μ A.1 = μ ((T \ S) ∪ A.1) := (measure_union hd hAm).symm
      _ ≤ μ T := measure_mono (union_subset sdiff_subset (A.2.2.trans hST))
  rw [hfull] at hbound
  apply le_antisymm _ bot_le
  change μ (T \ S) ≤ 0
  apply (ENNReal.add_le_add_iff_right (measure_ne_top μ T)).mp
  simpa only [μ, zero_add] using hbound

theorem measurable_of_subset_full_inner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S T : Set ((U : Filter ℕ).Product X)) (hST : S ⊆ T)
    (hT : MeasurableSet T)
    (hfull : internalInnerMeasure U hU S = loebMeasure U hU T) :
    MeasurableSet S ∧ S =ᵐ[loebMeasure U hU] T := by
  have hzero := loebMeasure_sdiff_eq_zero_of_full_inner U hU S T hST hfull
  have hdiff := measurable_of_loebMeasure_zero U hU (T \ S) hzero
  have hset : S = T \ (T \ S) := by
    ext x
    constructor
    · intro hx
      exact ⟨hST hx, fun h => h.2 hx⟩
    · rintro ⟨hxT, hx⟩
      by_contra hn
      exact hx ⟨hxT, hn⟩
  refine ⟨?_, hST.eventuallySubset.antisymm (ae_le_set.mpr hzero)⟩
  rw [hset]
  exact hT.diff hdiff

end Erdos335.Loeb

end
