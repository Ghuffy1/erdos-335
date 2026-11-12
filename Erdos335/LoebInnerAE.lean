import Erdos335.LoebMeasurableSetModel

/-!
# Inner measure and null changes
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance innerAELoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem internalInnerMeasure_le_of_ae_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S T : Set ((U : Filter ℕ).Product X)) (hST : S ≤ᵐ[loebMeasure U hU] T) :
    internalInnerMeasure U hU S ≤ internalInnerMeasure U hU T := by
  unfold internalInnerMeasure
  apply iSup_le
  intro D
  have hDm : MeasurableSet D.1 := by
    obtain ⟨A, hA⟩ := D.2.1
    rw [← hA]
    exact measurable_internalSet U A
  exact loeb_inner_measure_ge_of_ae_subset U hU D.1 T hDm (D.2.2.eventuallySubset.trans hST)

theorem internalInnerMeasure_congr_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S T : Set ((U : Filter ℕ).Product X)) (hST : S =ᵐ[loebMeasure U hU] T) :
    internalInnerMeasure U hU S = internalInnerMeasure U hU T :=
  le_antisymm (internalInnerMeasure_le_of_ae_subset U hU S T hST.le)
    (internalInnerMeasure_le_of_ae_subset U hU T S hST.symm.le)

end Erdos335.Loeb

end
