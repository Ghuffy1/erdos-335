import Erdos335.IrreducibleAEModels
import Erdos335.LoebAperiodicRestriction

/-!
# Structural hypotheses retained by almost-everywhere pair models
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance aeModelStructureLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_ae_pair_model_structure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B P Q : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hPm : MeasurableSet P) (hQm : MeasurableSet Q) (hPQm : MeasurableSet (P + Q))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B)
    (hPA : P =ᵐ[loebMeasure U hU] A) (hQB : Q =ᵐ[loebMeasure U hU] B)
    (hsum : P + Q =ᵐ[loebMeasure U hU] A + B) :
    0 < loebMeasure U hU P ∧ 0 < loebMeasure U hU Q ∧
      loebMeasure U hU (P + Q) = loebMeasure U hU P + loebMeasure U hU Q ∧
      MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) P Q ∧
      MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) P Q ∧
      ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
        MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
        0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
        ¬ ∀ t ∈ H, t +ᵥ (P + Q) =ᵐ[loebMeasure U hU] P + Q := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hPmass : μ P = μ A := measure_congr hPA
  have hQmass : μ Q = μ B := measure_congr hQB
  have hPpos : 0 < μ P := by rwa [hPmass]
  have hQpos : 0 < μ Q := by rwa [hQmass]
  have hPQfull : μ (P + Q) = μ P + μ Q := by
    rw [measure_congr hsum, hfull, hPmass, hQmass]
  have hPQirr : MeasureIrreducible μ (internalInnerMeasure U hU) P Q :=
    MeasureIrreducible.of_ae_pair (fun _ _ h => internalInnerMeasure_mono U hU h)
      hirr hAm hBm hPA.symm hQB.symm
      (internalInnerMeasure_congr_ae U hU _ _ hsum)
  have hPQnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < μ (H : Set _) → ¬ ∀ t ∈ H, t +ᵥ (P + Q) =ᵐ[μ] P + Q := by
    intro H hHm hHpos hperiod
    apply hnoAE H hHm hHpos
    intro t ht
    exact (loeb_vadd_congr_ae U hU _ _ t hsum.symm).trans ((hperiod t ht).trans hsum)
  have hPQne : MeasureNonextendible μ (internalInnerMeasure U hU) P Q := by
    apply loeb_nonextendible_of_no_essential_period U hU q P Q hPm hQm hPpos hQpos
      ((internalInnerMeasure_eq U hU _ hPQm).trans hPQfull)
    intro h hperiod
    apply hPQnoAE (naturalCyclicKernel U q h) (measurable_naturalCyclicKernel U q h)
      (naturalCyclicKernel_measure_pos U hU q h)
    intro t ht
    exact loeb_translate_ae_of_essential_period U hU q (P + Q) hPQm
      (naturalCyclicKernel U q h) (ae_le_set.mp hperiod.le) t ht
  exact ⟨hPpos, hQpos, hPQfull, hPQirr, hPQne, hPQnoAE⟩

end Erdos335.Loeb

end
