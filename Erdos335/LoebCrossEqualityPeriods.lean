import Erdos335.LoebOnePeriodicSummand
import Erdos335.LoebExtraCoset

/-!
# Periods in the two-cross-equality case

When both cross sums retain the full sum's inner measure, the critical
core inputs each fill their occupied stabilizer cosets. Both cross sums
are then measurable and essentially periodic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance crossEqualityPeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_reducible_equal_cross_core_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hApos : 0 < loebMeasure U hU Acore) (hBpos : 0 < loebMeasure U hU Bcore)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hcore : internalInnerMeasure U hU (Acore + Bcore) <
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hcrossleft : internalInnerMeasure U hU (A + Bcore) =
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hcrossright : internalInnerMeasure U hU (Acore + B) =
      loebMeasure U hU Acore + loebMeasure U hU Bcore) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (Acore + Bcore)
    loebMeasure U hU ((Acore + (H : Set G)) \ Acore) = 0 ∧
      loebMeasure U hU ((Bcore + (H : Set G)) \ Bcore) = 0 := by
  obtain ⟨_, _, _, _, _, _, hBperiod, _⟩ :=
    loeb_equality_extension_periodic_backgrounds U hU q Acore Bcore B
      hAcorem hBcorem hApos hBpos hBsub hcore hcrossright
  have hcore' : internalInnerMeasure U hU (Bcore + Acore) <
      loebMeasure U hU Bcore + loebMeasure U hU Acore := by simpa only [add_comm] using hcore
  have hcross' : internalInnerMeasure U hU (Bcore + A) =
      loebMeasure U hU Bcore + loebMeasure U hU Acore := by simpa only [add_comm] using hcrossleft
  obtain ⟨_, _, _, _, _, _, hAperiod, _⟩ :=
    loeb_equality_extension_periodic_backgrounds U hU q Bcore Acore A
      hBcorem hAcorem hBpos hApos hAsub hcore' hcross'
  exact ⟨by simpa only [add_comm Bcore Acore] using hAperiod, hBperiod⟩

theorem loeb_reducible_equal_cross_sum_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hApos : 0 < loebMeasure U hU Acore) (hBpos : 0 < loebMeasure U hU Bcore)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hcore : internalInnerMeasure U hU (Acore + Bcore) <
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hcrossleft : internalInnerMeasure U hU (A + Bcore) =
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hcrossright : internalInnerMeasure U hU (Acore + B) =
      loebMeasure U hU Acore + loebMeasure U hU Bcore) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (Acore + Bcore)
    MeasurableSet (A + Bcore) ∧ MeasurableSet (Acore + B) ∧
      (A + Bcore) + (H : Set G) =ᵐ[loebMeasure U hU] A + Bcore ∧
      (Acore + B) + (H : Set G) =ᵐ[loebMeasure U hU] Acore + B := by
  obtain ⟨_, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q Acore Bcore
    hAcorem hBcorem hApos hBpos hcore
  obtain ⟨hAperiod, hBperiod⟩ := loeb_reducible_equal_cross_core_periods U hU q Acore Bcore A B
    hAcorem hBcorem hApos hBpos hAsub hBsub hcore hcrossleft hcrossright
  obtain ⟨hleftm, hleftperiod⟩ := loeb_sum_with_essentially_periodic_summand U hU q _ hHm hHpos A Bcore hBperiod
  obtain ⟨hrightm, hrightperiod⟩ := loeb_sum_with_essentially_periodic_summand U hU q _ hHm hHpos B Acore hAperiod
  exact ⟨hleftm, by simpa only [add_comm B Acore] using hrightm, hleftperiod,
    by simpa only [add_comm B Acore] using hrightperiod⟩

end Erdos335.Loeb

end
