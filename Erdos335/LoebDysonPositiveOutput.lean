import Erdos335.LoebDysonOutput
import Erdos335.LoebInnerSumBounds

/-!
# The strict Dyson output has a positive periodic background
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance dysonPositiveOutputLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_strict_dyson_positive_background_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hIpos : 0 < loebMeasure U hU (A ∩ B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU ((A ∪ B) + (A ∩ B)) <
      loebMeasure U hU (A ∪ B) + loebMeasure U hU (A ∩ B))
    (hnotperiod : ¬ ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      (A + B) + (H : Set _) = A + B) :
    let H := AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      ((A ∪ B) + (A ∩ B))
    ∃ D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      ∃ p : QuasiPeriodicDecomposition (loebMeasure U hU) H D,
        D ⊆ A + B ∧ A + B =ᵐ[loebMeasure U hU] D ∧
        p.background = (A ∪ B) + (A ∩ B) ∧ 0 < loebMeasure U hU p.background := by
  obtain ⟨D, p, hDS, hSD, hBg⟩ := loeb_strict_dyson_quasiPeriodic_output_model U hU q A B
    hAm hBm hSm hIpos hfull hsmall hnotperiod
  refine ⟨D, p, hDS, hSD, hBg, ?_⟩
  rw [hBg]
  have hUnion : 0 < loebMeasure U hU (A ∪ B) :=
    hIpos.trans_le (measure_mono (inter_subset_left.trans subset_union_left))
  have hbound := loeb_left_measure_le_sum_inner U hU (A ∪ B) (A ∩ B)
    (hAm.union hBm) (nonempty_of_measure_ne_zero hIpos.ne')
  exact hUnion.trans_le (hbound.trans (internalInnerMeasure_le U hU _))

end Erdos335.Loeb

end
