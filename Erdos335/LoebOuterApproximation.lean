import Erdos335.LoebHull

/-!
# Loeb outer measure as an infimum over internal covers
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]

theorem loebMeasure_eq_iInf_internal_supersets
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) :
    loebMeasure U hU S =
      ⨅ T : {T : Set ((U : Filter ℕ).Product X) // T ∈ internalSets U ∧ S ⊆ T},
        loebMeasure U hU T.1 := by
  apply le_antisymm
  · exact le_iInf fun T => measure_mono T.2.2
  · apply le_of_forall_gt
    intro c hc
    obtain ⟨T, hTi, hST, hTc⟩ := exists_internal_cover_lt U hU S c hc
    exact (iInf_le (fun V : {V : Set ((U : Filter ℕ).Product X) //
      V ∈ internalSets U ∧ S ⊆ V} => loebMeasure U hU V.1) ⟨T, hTi, hST⟩).trans_lt hTc

end Erdos335.Loeb
