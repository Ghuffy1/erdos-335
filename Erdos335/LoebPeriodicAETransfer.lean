import Erdos335.LoebPeriodicExtension

/-!
# Transferring a periodic measurable model through null changes
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance periodicTransferLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_irreducible_periodic_ae_transfer
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B P Q : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hPm : MeasurableSet P) (hQm : MeasurableSet Q)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hAP : A =ᵐ[loebMeasure U hU] P) (hBQ : B =ᵐ[loebMeasure U hU] Q)
    (hPQm : MeasurableSet (P + Q))
    (hperiod : (P + Q) + (H : Set _) =ᵐ[loebMeasure U hU] P + Q)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hmodel : loebMeasure U hU (P + Q) = loebMeasure U hU P + loebMeasure U hU Q) :
    ∃ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ∧
      ((A + B) + (K : Set _) =ᵐ[loebMeasure U hU] A + B ∨
        ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
          loebMeasure U hU p.left.active = 0 ∧ loebMeasure U hU p.right.active = 0) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let C := A ∩ P
  let D := B ∩ Q
  have hCm : MeasurableSet C := hAm.inter hPm
  have hDm : MeasurableSet D := hBm.inter hQm
  have hCA : C =ᵐ[μ] A := by
    filter_upwards [hAP] with x hx
    change (x ∈ A ∧ x ∈ P) = (x ∈ A)
    rw [← hx]
    exact and_self _
  have hDB : D =ᵐ[μ] B := by
    filter_upwards [hBQ] with x hx
    change (x ∈ B ∧ x ∈ Q) = (x ∈ B)
    rw [← hx]
    exact and_self _
  have hCmass : μ C = μ A := measure_congr hCA
  have hDmass : μ D = μ B := measure_congr hDB
  have hcore : internalInnerMeasure U hU (C + D) = μ (P + Q) := by
    rw [hirr C D hCm hDm inter_subset_left inter_subset_left hCmass hDmass,
      hfull, hmodel, ← measure_congr hAP, ← measure_congr hBQ]
  have hsub : C + D ⊆ P + Q := add_subset_add inter_subset_right inter_subset_right
  have hcoreAE := (measurable_of_subset_full_inner U hU (C + D) (P + Q) hsub hPQm hcore).2
  have hcorePeriod : (C + D) + (H : Set G) =ᵐ[μ] C + D := by
    have hforward : (C + D) + (H : Set G) ≤ᵐ[μ] C + D :=
      (add_subset_add hsub Subset.rfl).eventuallySubset.trans (hperiod.le.trans hcoreAE.ge)
    have hback : C + D ⊆ (C + D) + (H : Set G) :=
      fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
    exact hforward.antisymm hback.eventuallySubset
  exact loeb_irreducible_extension_of_periodic_core U hU q H C D A B hHm hHpos
    hCm hDm hAm hBm hApos hBpos inter_subset_left inter_subset_left
    hCmass.symm hDmass.symm hirr hfull hcorePeriod

end Erdos335.Loeb

end
