import Erdos335.LoebInner
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Inner measure from internal subsets

Internal inner approximation identifies this supremum with Loeb measure
on measurable sets. Its monotonicity applies to arbitrary sumsets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal symmDiff

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]

def internalInnerMeasure (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) : ℝ≥0∞ :=
  ⨆ T : {T : Set ((U : Filter ℕ).Product X) // T ∈ internalSets U ∧ T ⊆ S},
    loebMeasure U hU T.1

theorem internalInnerMeasure_mono
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    {S T : Set ((U : Filter ℕ).Product X)} (hST : S ⊆ T) :
    internalInnerMeasure U hU S ≤ internalInnerMeasure U hU T := by
  unfold internalInnerMeasure
  apply iSup_le
  intro A
  exact le_iSup_of_le ⟨A.1, A.2.1, A.2.2.trans hST⟩ le_rfl

theorem internalInnerMeasure_le
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) :
    internalInnerMeasure U hU S ≤ loebMeasure U hU S := by
  unfold internalInnerMeasure
  exact iSup_le (fun T => measure_mono T.2.2)

theorem internalInnerMeasure_eq
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (hS : MeasurableSet[loebMeasurableSpace U] S) :
    internalInnerMeasure U hU S = loebMeasure U hU S := by
  refine le_antisymm (internalInnerMeasure_le U hU S) ?_
  let ε (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound (n : ℕ) : loebMeasure U hU S ≤ internalInnerMeasure U hU S + ε n := by
    obtain ⟨T, hTi, hTS, herr⟩ := exists_internal_inner_approximation U hU S hS (ε n) (by
      dsimp [ε]
      positivity)
    have hsub : S ⊆ T ∪ (S ∆ T) := by
      intro x hx
      by_cases ht : x ∈ T
      · exact Or.inl ht
      · exact Or.inr (Or.inl ⟨hx, ht⟩)
    calc
      loebMeasure U hU S ≤ loebMeasure U hU (T ∪ (S ∆ T)) := measure_mono hsub
      _ ≤ loebMeasure U hU T + loebMeasure U hU (S ∆ T) := measure_union_le _ _
      _ ≤ internalInnerMeasure U hU S + ε n := add_le_add
        (le_iSup (fun V : {V : Set ((U : Filter ℕ).Product X) // V ∈ internalSets U ∧ V ⊆ S} =>
          loebMeasure U hU V.1) ⟨T, hTi, hTS⟩) herr.le
  have hlim : Tendsto (fun n => internalInnerMeasure U hU S + ε n) atTop
      (𝓝 (internalInnerMeasure U hU S)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hε
  exact ge_of_tendsto' hlim hbound

theorem internalInnerMeasure_eq_iSup_measurable
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) :
    internalInnerMeasure U hU S =
      ⨆ T : {T : Set ((U : Filter ℕ).Product X) //
        MeasurableSet[loebMeasurableSpace U] T ∧ T ⊆ S}, loebMeasure U hU T.1 := by
  apply le_antisymm
  · unfold internalInnerMeasure
    apply iSup_le
    intro T
    have hTm : MeasurableSet[loebMeasurableSpace U] T.1 := by
      obtain ⟨A, hA⟩ := T.2.1
      rw [← hA]
      exact measurable_internalSet U A
    exact le_iSup_of_le ⟨T.1, hTm, T.2.2⟩ le_rfl
  · apply iSup_le
    intro T
    rw [← internalInnerMeasure_eq U hU T.1 T.2.1]
    exact internalInnerMeasure_mono U hU T.2.2

theorem ultraCount_le_internalInnerMeasure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ∀ n, Set (X n)) (S : Set ((U : Filter ℕ).Product X))
    (hAS : internalSet U A ⊆ S) :
    ultraCount U A ≤ internalInnerMeasure U hU S := by
  rw [← loebMeasure_internal U hU A]
  exact le_iSup_of_le ⟨internalSet U A, ⟨A, rfl⟩, hAS⟩ le_rfl

theorem exists_internal_subset_measure_gt
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (hS : MeasurableSet[loebMeasurableSpace U] S)
    (r : ℝ≥0∞) (hr : r < loebMeasure U hU S) :
    ∃ A : ∀ n, Set (X n), internalSet U A ⊆ S ∧ r < loebMeasure U hU (internalSet U A) := by
  rw [← internalInnerMeasure_eq U hU S hS] at hr
  obtain ⟨T, hT⟩ := lt_iSup_iff.mp hr
  obtain ⟨A, hA⟩ := T.2.1
  refine ⟨A, ?_, ?_⟩
  · rw [hA]
    exact T.2.2
  · rwa [hA]

end Erdos335.Loeb

end
