import Erdos335.LoebFullMeasureRestriction
import Erdos335.LoebNonextendiblePeriods
import Erdos335.LoebEssentialStabilizer
import Erdos335.LoebTranslationStructure

/-!
# Full-measure restriction of an aperiodic irreducible pair

The restricted sum agrees almost everywhere with the original sum.
Absence of positive translation periods passes through this equality
and yields nonextendibility of the restricted equality pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance aperiodicRestrictionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_aperiodic_full_measure_restriction
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B P Q : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hPm : MeasurableSet P) (hQm : MeasurableSet Q) (hSm : MeasurableSet (A + B))
    (hPpos : 0 < loebMeasure U hU P) (hQpos : 0 < loebMeasure U hU Q)
    (hPA : P ⊆ A) (hQB : Q ⊆ B)
    (hPmass : loebMeasure U hU P = loebMeasure U hU A)
    (hQmass : loebMeasure U hU Q = loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    MeasurableSet (P + Q) ∧ P + Q =ᵐ[loebMeasure U hU] A + B ∧
    loebMeasure U hU (P + Q) = loebMeasure U hU P + loebMeasure U hU Q ∧
    MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) P Q ∧
    MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) P Q ∧
    ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (P + Q) =ᵐ[loebMeasure U hU] P + Q := by
  obtain ⟨hPQm, hPQae, hPQfull, hPQirr⟩ := loeb_irreducible_full_measure_restriction U hU q
    A B P Q hPm hQm hSm hPA hQB hPmass hQmass hirr hfull
  have hPQnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (P + Q) =ᵐ[loebMeasure U hU] P + Q := by
    intro H hHm hHpos hp
    apply hnoAE H hHm hHpos
    intro t ht
    exact (loeb_vadd_congr_ae U hU (A + B) (P + Q) t hPQae.symm).trans ((hp t ht).trans hPQae)
  have hPQne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) P Q := by
    apply loeb_nonextendible_of_no_essential_period U hU q P Q hPm hQm hPpos hQpos
      ((internalInnerMeasure_eq U hU _ hPQm).trans hPQfull)
    intro h hp
    apply hPQnoAE (naturalCyclicKernel U q h) (measurable_naturalCyclicKernel U q h)
      (naturalCyclicKernel_measure_pos U hU q h)
    intro t ht
    exact loeb_translate_ae_of_essential_period U hU q (P + Q) hPQm
      (naturalCyclicKernel U q h) (ae_le_set.mp hp.le) t ht
  exact ⟨hPQm, hPQae, hPQfull, hPQirr, hPQne, hPQnoAE⟩

end Erdos335.Loeb

end
