import Erdos335.LoebCrossEqualityPeriods
import Erdos335.LoebPeriodicEquality
import Erdos335.LoebInnerAbsorption
import Erdos335.LoebFullSaturations

/-!
# The common periodic envelope in the cross-equality case
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance crossEqualityEnvelopeLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_periodic_saturations_eq_of_common_full_inner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (S X Y : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hXm : MeasurableSet X) (hYm : MeasurableSet Y) (hXS : X ⊆ S) (hYS : Y ⊆ S)
    (hXfull : internalInnerMeasure U hU S = loebMeasure U hU X)
    (hYfull : internalInnerMeasure U hU S = loebMeasure U hU Y)
    (hXperiod : X + (H : Set _) =ᵐ[loebMeasure U hU] X)
    (hYperiod : Y + (H : Set _) =ᵐ[loebMeasure U hU] Y) :
    X + (H : Set _) = Y + (H : Set _) := by
  have hXYzero := loeb_measure_sdiff_zero_of_full_inner U hU S Y X hYm hXm hYS hXS hYfull
  have hYXzero := loeb_measure_sdiff_zero_of_full_inner U hU S X Y hXm hYm hXS hYS hXfull
  have hXY : X =ᵐ[loebMeasure U hU] Y := (ae_le_set.mpr hXYzero).antisymm (ae_le_set.mpr hYXzero)
  have hXsaturated : (X + (H : Set _)) + (H : Set _) = X + (H : Set _) := by
    rw [add_assoc, coe_add_coe]
  have hYsaturated : (Y + (H : Set _)) + (H : Set _) = Y + (H : Set _) := by
    rw [add_assoc, coe_add_coe]
  exact loeb_periodic_sets_eq_of_ae U hU q H hHpos _ _ hXsaturated hYsaturated
    (hXperiod.trans (hXY.trans hYperiod.symm))

theorem loeb_cross_equality_periodic_envelope
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
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hfull : internalInnerMeasure U hU (A + B) =
      loebMeasure U hU Acore + loebMeasure U hU Bcore) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (Acore + Bcore)
    let T := (A + Bcore) + (H : Set G)
    T = (Acore + B) + (H : Set G) ∧
      loebMeasure U hU T = loebMeasure U hU Acore + loebMeasure U hU Bcore ∧
      ∃ g ∉ Acore + Bcore, T = (Acore + Bcore) ∪ (g +ᵥ (H : Set G)) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let H := AddAction.stabilizer G (Acore + Bcore)
  let C := Acore + Bcore
  let T := (A + Bcore) + (H : Set G)
  obtain ⟨hCm, hHm, hHpos, hidentity⟩ := loeb_measurable_kneser_identity U hU q Acore Bcore
    hAcorem hBcorem hApos hBpos hcore
  obtain ⟨hAperiod, hBperiod⟩ := loeb_reducible_equal_cross_core_periods U hU q Acore Bcore A B
    hAcorem hBcorem hApos hBpos hAsub hBsub hcore hcrossleft hcrossright
  obtain ⟨hXm, hYm, hXperiod, hYperiod⟩ := loeb_reducible_equal_cross_sum_periods U hU q Acore Bcore A B
    hAcorem hBcorem hApos hBpos hAsub hBsub hcore hcrossleft hcrossright
  have hXfull : internalInnerMeasure U hU (A + B) = μ (A + Bcore) := by
    rw [← internalInnerMeasure_eq U hU (A + Bcore) hXm]
    exact hfull.trans hcrossleft.symm
  have hYfull : internalInnerMeasure U hU (A + B) = μ (Acore + B) := by
    rw [← internalInnerMeasure_eq U hU (Acore + B) hYm]
    exact hfull.trans hcrossright.symm
  have hsame := loeb_periodic_saturations_eq_of_common_full_inner U hU q H hHpos
    (A + B) (A + Bcore) (Acore + B) hXm hYm
    (add_subset_add Subset.rfl hBsub) (add_subset_add hAsub Subset.rfl)
    hXfull hYfull hXperiod hYperiod
  have hTmass : μ T = μ Acore + μ Bcore := by
    have h := measure_congr hXperiod
    change μ T = μ (A + Bcore) at h
    rw [h, ← internalInnerMeasure_eq U hU (A + Bcore) hXm]
    exact hcrossleft
  have hAmass := loeb_measure_saturation_eq_of_essential_period U hU H Acore hAcorem hAperiod
  have hBmass := loeb_measure_saturation_eq_of_essential_period U hU H Bcore hBcorem hBperiod
  have hmass : μ T = μ C + μ (H : Set G) := by
    rw [hAmass, hBmass] at hidentity
    exact hTmass.trans hidentity
  have hCT : C ⊆ T := by
    intro x hx
    exact ⟨x, add_subset_add hAsub (show Bcore ⊆ Bcore from Subset.rfl) hx, 0, H.zero_mem, add_zero x⟩
  have hCperiod : C + (H : Set G) = C := by
    apply subset_antisymm
    · rintro x ⟨c, hc, k, hk, rfl⟩
      have hfix : k +ᵥ C = C := hk
      rw [← hfix]
      exact ⟨c, hc, add_comm k c⟩
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hTperiod : T + (H : Set G) = T := by
    dsimp only [T]
    rw [add_assoc, coe_add_coe]
  have hTm : MeasurableSet T :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos (A + Bcore)
  exact ⟨hsame, hTmass, loeb_periodic_extension_by_one_coset U hU q H hHm hHpos C T hCm hTm hCT hCperiod hTperiod hmass⟩

end Erdos335.Loeb

end
