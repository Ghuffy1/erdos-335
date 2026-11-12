import Erdos335.LoebIrreduciblePeriods

/-!
# A quasi-periodic input has positive active mass in the aperiodic case
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicActivePositiveLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_active_positive_of_irreducible
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    0 < loebMeasure U hU p.active := by
  by_contra hn
  have hzero : loebMeasure U hU p.active = 0 := le_antisymm (not_lt.mp hn) bot_le
  have hAm : MeasurableSet A := p.partition.symm ▸ (p.background_measurable.union p.active_measurable)
  have hp := loeb_quasiPeriodic_null_active_ae_periods U hU q A H p hzero
  exact hnoAE (loeb_irreducible_sum_ae_periods_of_input U hU q A B hAm hBm hSm H hHm hHpos hirr hp)

end Erdos335.Loeb

end
