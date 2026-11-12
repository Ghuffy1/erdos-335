import Erdos335.LoebPositiveQuasiPeriodic
import Erdos335.LoebPeriodicExtension
import Erdos335.LoebZeroActiveCore

/-!
# A quasi-periodic input with a positive background

The positive-active case follows from strict-background recovery. A null
active part gives an essentially periodic full-measure core, and the
existing irreducible extension theorem recovers the original pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicInputLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_pair_of_nonnull_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hBgpos : 0 < loebMeasure U hU p.background)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  by_cases hActpos : 0 < loebMeasure U hU p.active
  · exact loeb_quasiPeriodic_pair_of_positive_background U hU q A B H hHm hHpos p
      hBm hSm hBgpos hActpos hBpos hfull hirr hne hnotperiod
  have hActzero : loebMeasure U hU p.active = 0 := le_antisymm (not_lt.mp hActpos) bot_le
  have hAm : MeasurableSet A := p.partition.symm ▸ (p.background_measurable.union p.active_measurable)
  have hparts : Disjoint p.background p.active := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp p.separated ⟨x, hy, 0, H.zero_mem, add_zero x⟩ hx
  have hAmass : loebMeasure U hU A = loebMeasure U hU p.background := by
    calc
      loebMeasure U hU A = loebMeasure U hU (p.background ∪ p.active) :=
        congrArg (loebMeasure U hU) p.partition
      _ = loebMeasure U hU p.background := by
        rw [measure_union hparts p.active_measurable, hActzero, add_zero]
  have hbgsub : p.background ⊆ A := subset_union_left.trans p.partition.ge
  have hperiod := (loeb_sum_with_essentially_periodic_summand U hU q H hHm hHpos
    B p.background p.background_periodic).2
  rw [add_comm B p.background] at hperiod
  obtain ⟨K, hKm, hKpos, hcase⟩ := loeb_irreducible_extension_of_periodic_core U hU q H
    p.background B A B hHm hHpos p.background_measurable hBm hAm hBm hApos hBpos
    hbgsub Subset.rfl hAmass rfl hirr
    ((internalInnerMeasure_eq U hU _ hSm).trans hfull) hperiod
  rcases hcase with hp | ⟨r, _, _⟩
  · exact False.elim (hnotperiod ⟨K, hKm, hKpos, hp⟩)
  · exact ⟨r⟩

end Erdos335.Loeb

end
