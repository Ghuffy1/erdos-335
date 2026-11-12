import Erdos335.LoebFiniteUnionPeriod
import Erdos335.LoebMeasurableKneser

/-!
# A nonperiodic finite union has a noncritical component

If every positive measurable summand pair has a strict deficit, Kneser
gives a positive period for each component. Their finite intersection
is then a positive period of the whole union.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance finiteCriticalUnionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_finite_union_of_critical_sums_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {I : Type*} [Fintype I]
    (A B : I → Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : ∀ i, MeasurableSet (A i)) (hBm : ∀ i, MeasurableSet (B i))
    (hApos : ∀ i, 0 < loebMeasure U hU (A i)) (hBpos : ∀ i, 0 < loebMeasure U hU (B i))
    (hsmall : ∀ i, internalInnerMeasure U hU (A i + B i) <
      loebMeasure U hU (A i) + loebMeasure U hU (B i)) :
    ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      (⋃ i, A i + B i) + (H : Set _) = ⋃ i, A i + B i := by
  classical
  choose h hm hp hperiod using fun i =>
    loeb_measurable_subcritical_period U hU q (A i) (B i) (hAm i) (hBm i) (hApos i) (hBpos i) (hsmall i)
  obtain ⟨H, hHm, hHpos, hHperiod⟩ := loeb_finite_union_has_positive_period U hU q Finset.univ
    (fun i => A i + B i) (fun i => naturalCyclicKernel U q (h i))
    (fun i _ => hm i) (fun i _ => hp i) (fun i _ => hperiod i)
  exact ⟨H, hHm, hHpos, by simpa only [Finset.mem_univ, iUnion_true] using hHperiod⟩

theorem loeb_nonperiodic_finite_union_has_noncritical_component
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {I : Type*} [Fintype I]
    (A B : I → Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : ∀ i, MeasurableSet (A i)) (hBm : ∀ i, MeasurableSet (B i))
    (hApos : ∀ i, 0 < loebMeasure U hU (A i)) (hBpos : ∀ i, 0 < loebMeasure U hU (B i))
    (hnotperiod : ¬ ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      (⋃ i, A i + B i) + (H : Set _) = ⋃ i, A i + B i) :
    ∃ i, loebMeasure U hU (A i) + loebMeasure U hU (B i) ≤ internalInnerMeasure U hU (A i + B i) := by
  by_contra h
  push_neg at h
  exact hnotperiod (loeb_finite_union_of_critical_sums_periodic U hU q A B hAm hBm hApos hBpos h)

end Erdos335.Loeb

end
