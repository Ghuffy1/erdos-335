import Erdos335.LoebAEPeriodCore
import Erdos335.LoebEssentialStabilizer
import Erdos335.LoebPeriodicExtension
import Erdos335.LoebNonextendiblePeriods

/-!
# Transferring essential translation periods

Irreducibility transfers a subgroup of translation periods from either
input to the sumset. Nonextendibility transfers sumset periods back to
the inputs. Positive sumset periods consequently enter the existing
periodic-core classification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance aePeriodTransferLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_irreducible_sum_ae_periods_of_input
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hperiod : ∀ t ∈ H, t +ᵥ A =ᵐ[loebMeasure U hU] A) :
    ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B := by
  obtain ⟨C, hCm, hCA, hCmass, hCperiod⟩ :=
    loeb_essential_periodic_core_of_ae_periods U hU q A hAm H hHm hHpos hperiod
  obtain ⟨hTm, hTperiod⟩ := loeb_sum_with_essentially_periodic_summand U hU q H hHm hHpos B C hCperiod
  rw [add_comm B C] at hTm hTperiod
  have hinner : internalInnerMeasure U hU (C + B) = loebMeasure U hU (A + B) :=
    (hirr C B hCm hBm hCA Subset.rfl hCmass rfl).trans (internalInnerMeasure_eq U hU _ hSm)
  have hTS := (measurable_of_subset_full_inner U hU (C + B) (A + B)
    (add_subset_add hCA Subset.rfl) hSm hinner).2
  intro t ht
  have hTfix := loeb_translate_ae_of_essential_period U hU q (C + B) hTm H
    (ae_le_set.mp hTperiod.le) t ht
  exact (loeb_vadd_congr_ae U hU (A + B) (C + B) t hTS.symm).trans (hTfix.trans hTS)

theorem loeb_ae_periodic_sum_core_classification
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hperiod : ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    ∃ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ∧
      ((A + B) + (K : Set _) =ᵐ[loebMeasure U hU] A + B ∨
        ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
          loebMeasure U hU p.left.active = 0 ∧ loebMeasure U hU p.right.active = 0) := by
  have hAperiod (t) (ht : t ∈ H) := (loeb_nonextendible_inputs_ae_period U hU A B hAm hBm hne t (hperiod t ht)).1
  have hBperiod (t) (ht : t ∈ H) := (loeb_nonextendible_inputs_ae_period U hU A B hAm hBm hne t (hperiod t ht)).2
  obtain ⟨C, hCm, hCA, hCmass, hCp⟩ :=
    loeb_essential_periodic_core_of_ae_periods U hU q A hAm H hHm hHpos hAperiod
  obtain ⟨D, hDm, hDB, hDmass, _⟩ :=
    loeb_essential_periodic_core_of_ae_periods U hU q B hBm H hHm hHpos hBperiod
  have hCDperiod := (loeb_sum_with_essentially_periodic_summand U hU q H hHm hHpos D C hCp).2
  rw [add_comm D C] at hCDperiod
  exact loeb_irreducible_extension_of_periodic_core U hU q H C D A B hHm hHpos hCm hDm
    hAm hBm hApos hBpos hCA hDB hCmass.symm hDmass.symm hirr hfull hCDperiod

end Erdos335.Loeb

end
