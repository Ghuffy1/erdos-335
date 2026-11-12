import Erdos335.LoebComplementDuality
import Erdos335.LoebAEPeriodOperations
import Erdos335.LoebIrreduciblePeriods
import Erdos335.LoebZeroActiveCore

/-!
# Irreducibility and nonextendibility of the complement dual

An irreducible nonextendible equality pair with no positive subgroup of
essential translation periods has a complement dual with the same three
properties. This is the structural part of Griesmer's Lemma 5.14.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance complementStructureLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_complement_dual_structure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hCpos : 0 < loebMeasure U hU (A + B)ᶜ)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) (-B) (A + B)ᶜ ∧
    MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) (-B) (A + B)ᶜ ∧
    ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ ((-B) + (A + B)ᶜ) =ᵐ[loebMeasure U hU] (-B) + (A + B)ᶜ := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let C := (A + B)ᶜ
  let E := (-B) + C
  have hnegBm : MeasurableSet (-B) := hBm.preimage (measurable_loeb_neg U hU)
  have hnegBpos : 0 < μ (-B) := by rwa [loebMeasure_neg U hU B hBm]
  obtain ⟨hEm, hEae, hdual⟩ := loeb_nonextendible_complement_duality U hU q A B
    hAm hBm hSm hBpos hCpos hfull hne
  have noA (H : AddSubgroup G) (hHm : MeasurableSet (H : Set G)) (hHpos : 0 < μ (H : Set G))
      (hp : ∀ t ∈ H, t +ᵥ A =ᵐ[μ] A) : False :=
    hnoAE H hHm hHpos (loeb_irreducible_sum_ae_periods_of_input U hU q A B hAm hBm hSm H hHm hHpos hirr hp)
  have noB (H : AddSubgroup G) (hHm : MeasurableSet (H : Set G)) (hHpos : 0 < μ (H : Set G))
      (hp : ∀ t ∈ H, t +ᵥ B =ᵐ[μ] B) : False := by
    have hsum := loeb_irreducible_sum_ae_periods_of_input U hU q B A hBm hAm
      (by simpa only [add_comm B A] using hSm) H hHm hHpos hirr.swap hp
    apply hnoAE H hHm hHpos
    simpa only [add_comm B A] using hsum
  have noE (H : AddSubgroup G) (hHm : MeasurableSet (H : Set G)) (hHpos : 0 < μ (H : Set G)) :
      ¬ ∀ t ∈ H, t +ᵥ E =ᵐ[μ] E := by
    intro hp
    apply noA H hHm hHpos
    intro t ht
    have hcompl : t +ᵥ Aᶜ =ᵐ[μ] Aᶜ :=
      (loeb_vadd_congr_ae U hU E Aᶜ t hEae).symm.trans ((hp t ht).trans hEae)
    exact loeb_ae_period_compl U hU A t hcompl
  have hdualIrr : MeasureIrreducible μ (internalInnerMeasure U hU) (-B) C := by
    apply loeb_irreducible_of_no_positive_ae_periods U hU q (-B) C hnegBm hSm.compl hEm
      hnegBpos hCpos hdual
    intro H hHm hHpos hp
    rcases hp with hpB | hpC | hpE
    · apply noB H hHm hHpos
      intro t ht
      exact loeb_ae_period_of_neg U hU B t (hpB (-t) (H.neg_mem ht))
    · apply hnoAE H hHm hHpos
      intro t ht
      exact loeb_ae_period_compl U hU (A + B) t (hpC t ht)
    · exact noE H hHm hHpos hpE
  have hdualNe : MeasureNonextendible μ (internalInnerMeasure U hU) (-B) C := by
    apply loeb_nonextendible_of_no_essential_period U hU q (-B) C hnegBm hSm.compl hnegBpos hCpos hdual
    intro h hp
    have hHm := measurable_naturalCyclicKernel U q h
    have hHpos := naturalCyclicKernel_measure_pos U hU q h
    apply noE (naturalCyclicKernel U q h) hHm hHpos
    intro t ht
    exact loeb_translate_ae_of_essential_period U hU q E hEm (naturalCyclicKernel U q h)
      (ae_le_set.mp hp.le) t ht
  exact ⟨hdualIrr, hdualNe, noE⟩

end Erdos335.Loeb

end
