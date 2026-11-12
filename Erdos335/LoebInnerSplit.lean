import Erdos335.LoebInnerMeasure

/-!
# Splitting inner measure along a measurable subset

The formula applies even when the whole set is not measurable. It
isolates the inner measure of the exceptional output of a critical pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]

local instance innerSplitLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem internalInnerMeasure_eq_add_sdiff
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S M : Set ((U : Filter ℕ).Product X)) (hM : MeasurableSet M) (hMS : M ⊆ S) :
    internalInnerMeasure U hU S = loebMeasure U hU M + internalInnerMeasure U hU (S \ M) := by
  let μ := loebMeasure (X := X) U hU
  apply le_antisymm
  · rw [internalInnerMeasure_eq_iSup_measurable]
    apply iSup_le
    intro T
    have hdiff : μ (T.1 \ M) ≤ internalInnerMeasure U hU (S \ M) := by
      rw [← internalInnerMeasure_eq U hU (T.1 \ M) (T.2.1.diff hM)]
      exact internalInnerMeasure_mono U hU (sdiff_subset_sdiff_left T.2.2)
    calc
      μ T.1 = μ (T.1 ∩ M) + μ (T.1 \ M) := (measure_inter_add_sdiff T.1 hM).symm
      _ ≤ μ M + internalInnerMeasure U hU (S \ M) :=
        add_le_add (measure_mono inter_subset_right) hdiff
  · rw [internalInnerMeasure_eq_iSup_measurable U hU (S \ M)]
    let I := {T : Set ((U : Filter ℕ).Product X) // MeasurableSet T ∧ T ⊆ S \ M}
    letI : Nonempty I := ⟨⟨∅, MeasurableSet.empty, empty_subset _⟩⟩
    rw [ENNReal.add_iSup]
    apply iSup_le
    intro T
    have hdisj : Disjoint M T.1 := by
      apply Set.disjoint_left.mpr
      intro x hxM hxT
      exact (T.2.2 hxT).2 hxM
    calc
      μ M + μ T.1 = μ (M ∪ T.1) := (measure_union hdisj T.2.1).symm
      _ = internalInnerMeasure U hU (M ∪ T.1) :=
        (internalInnerMeasure_eq U hU _ (hM.union T.2.1)).symm
      _ ≤ internalInnerMeasure U hU S :=
        internalInnerMeasure_mono U hU (union_subset hMS (T.2.2.trans sdiff_subset))

end Erdos335.Loeb

end
