import Erdos335.LoebQuasiPeriodicSumModel
import Erdos335.LoebReducibleEquality
import Erdos335.LoebNonextendiblePeriods

/-!
# Structural alternatives for a pair with the same equality sumset

A reducible equality pair gives a quasi-periodic model of its sumset.
For an aperiodic original pair this recovers a quasi-periodic original
pair. The remaining alternative retains the structural hypotheses
needed for another Dyson step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance equalSumStructureLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_equal_sum_model_structure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B P Q : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hCpos : 0 < loebMeasure U hU (A + B)ᶜ)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B)
    (hPm : MeasurableSet P) (hQm : MeasurableSet Q) (hPQm : MeasurableSet (P + Q))
    (hPpos : 0 < loebMeasure U hU P) (hQpos : 0 < loebMeasure U hU Q)
    (hPQfull : loebMeasure U hU (P + Q) = loebMeasure U hU P + loebMeasure U hU Q)
    (hPQae : P + Q =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) ∨
      (MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) P Q ∧
       MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) P Q ∧
       ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
         MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
         0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
         ¬ ∀ t ∈ H, t +ᵥ (P + Q) =ᵐ[loebMeasure U hU] P + Q) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hPQnoAE : ∀ H : AddSubgroup G, MeasurableSet (H : Set G) → 0 < μ (H : Set G) →
      ¬ ∀ t ∈ H, t +ᵥ (P + Q) =ᵐ[μ] P + Q := by
    intro H hHm hHpos hp
    apply hnoAE H hHm hHpos
    intro t ht
    exact (loeb_vadd_congr_ae U hU (A + B) (P + Q) t hPQae.symm).trans ((hp t ht).trans hPQae)
  have hPQinner : internalInnerMeasure U hU (P + Q) = μ P + μ Q :=
    (internalInnerMeasure_eq U hU _ hPQm).trans hPQfull
  have hPQne : MeasureNonextendible μ (internalInnerMeasure U hU) P Q := by
    apply loeb_nonextendible_of_no_essential_period U hU q P Q hPm hQm hPpos hQpos hPQinner
    intro h hp
    apply hPQnoAE (naturalCyclicKernel U q h) (measurable_naturalCyclicKernel U q h)
      (naturalCyclicKernel_measure_pos U hU q h)
    intro t ht
    exact loeb_translate_ae_of_essential_period U hU q (P + Q) hPQm
      (naturalCyclicKernel U q h) (ae_le_set.mp hp.le) t ht
  rcases loeb_irreducible_or_reducible U hU q P Q with hPQirr | hred
  · exact Or.inr ⟨hPQirr, hPQne, hPQnoAE⟩
  · obtain ⟨P₀, Q₀, hP₀m, hQ₀m, hP₀P, hQ₀Q, hP₀mass, hQ₀mass, hsmall⟩ := hred
    have hcore : internalInnerMeasure U hU (P₀ + Q₀) < μ P₀ + μ Q₀ := by
      rw [hP₀mass, hQ₀mass]
      exact hsmall.trans_eq hPQinner
    have hP₀pos : 0 < μ P₀ := by rwa [hP₀mass]
    have hQ₀pos : 0 < μ Q₀ := by rwa [hQ₀mass]
    obtain ⟨_, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q P₀ Q₀
      hP₀m hQ₀m hP₀pos hQ₀pos hcore
    rcases loeb_reducible_equality_dichotomy U hU q P₀ Q₀ P Q hP₀m hQ₀m hPm hQm
      hP₀pos hQ₀pos hP₀P hQ₀Q hP₀mass.symm hQ₀mass.symm hcore hPQinner with hp | ⟨p, _⟩
    · exfalso
      apply hPQnoAE (AddAction.stabilizer G (P₀ + Q₀)) hHm hHpos
      intro t ht
      exact loeb_translate_ae_of_essential_period U hU q (P + Q) hPQm
        (AddAction.stabilizer G (P₀ + Q₀)) (ae_le_set.mp hp.le) t ht
    · exact Or.inl (loeb_quasiPeriodic_pair_of_equal_sum_model U hU q A B P Q p hPQm hPQae
        hAm hBm hSm hApos hBpos hCpos hfull hirr hne hnoAE)

end Erdos335.Loeb

end
