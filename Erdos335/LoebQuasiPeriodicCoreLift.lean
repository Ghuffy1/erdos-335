import Erdos335.LoebPeriodicExtension
import Erdos335.LoebZeroActiveCore
import Erdos335.LoebPositiveQuasiPeriodicLift
import Erdos335.LoebExtendible

/-!
# Lifting a measurable quasi-periodic core

An irreducible equality pair that is a full-measure extension of a
measurable quasi-periodic core has a finite essential period or a
quasi-periodic decomposition. The proof includes extendible cores,
null active pieces, and two positive active pieces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicCoreLiftLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_irreducible_extension_of_quasiPeriodic_core
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hA'm : MeasurableSet A') (hB'm : MeasurableSet B')
    (hA'pos : 0 < loebMeasure U hU A') (hB'pos : 0 < loebMeasure U hU B')
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hAmass : loebMeasure U hU A' = loebMeasure U hU A)
    (hBmass : loebMeasure U hU B' = loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A' B')
    (hCm : MeasurableSet (A + B))
    (hfull : internalInnerMeasure U hU (A' + B') = loebMeasure U hU A' + loebMeasure U hU B') :
    (∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      (A' + B') + (H : Set _) =ᵐ[loebMeasure U hU] A' + B') ∨
      Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A' B') := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let Output : Prop :=
    (∃ H : AddSubgroup G, MeasurableSet (H : Set G) ∧ 0 < μ (H : Set G) ∧
      (A' + B') + (H : Set G) =ᵐ[μ] A' + B') ∨
      Nonempty (QuasiPeriodicPairData μ (internalInnerMeasure U hU) A' B')
  change Output
  have hAm : MeasurableSet A := p.left.partition.symm ▸
    (p.left.background_measurable.union p.left.active_measurable)
  have hBm : MeasurableSet B := p.right.partition.symm ▸
    (p.right.background_measurable.union p.right.active_measurable)
  have hfinish (K : AddSubgroup G) (hKm : MeasurableSet (K : Set G)) (hKpos : 0 < μ (K : Set G))
      (hcase : (A' + B') + (K : Set G) =ᵐ[μ] A' + B' ∨
        ∃ r : QuasiPeriodicPairData μ (internalInnerMeasure U hU) A' B',
          μ r.left.active = 0 ∧ μ r.right.active = 0) : Output := by
    rcases hcase with hperiod | ⟨r, _, _⟩
    · exact Or.inl ⟨K, hKm, hKpos, hperiod⟩
    · exact Or.inr ⟨r⟩
  have hperiodic (H : AddSubgroup G) (hHm : MeasurableSet (H : Set G)) (hHpos : 0 < μ (H : Set G))
      (hperiod : (A + B) + (H : Set G) =ᵐ[μ] A + B) : Output := by
    obtain ⟨K, hKm, hKpos, hcase⟩ := loeb_irreducible_extension_of_periodic_core U hU q H A B A' B'
      hHm hHpos hAm hBm hA'm hB'm hA'pos hB'pos hAA' hBB' hAmass hBmass hirr hfull hperiod
    exact hfinish K hKm hKpos hcase
  by_cases hperiod : (A + B) + (p.period : Set G) =ᵐ[μ] A + B
  · exact hperiodic p.period p.period_measurable p.period_positive hperiod
  have hcoreInner : internalInnerMeasure U hU (A + B) = internalInnerMeasure U hU (A' + B') :=
    hirr A B hAm hBm hAA' hBB' hAmass.symm hBmass.symm
  have hcoreMeasure : μ (A + B) = μ A + μ B := by
    calc
      μ (A + B) = internalInnerMeasure U hU (A + B) := (internalInnerMeasure_eq U hU (A + B) hCm).symm
      _ = internalInnerMeasure U hU (A' + B') := hcoreInner
      _ = μ A' + μ B' := hfull
      _ = μ A + μ B := by rw [hAmass, hBmass]
  have hfullCore : internalInnerMeasure U hU (A' + B') = μ (A + B) :=
    hcoreInner.symm.trans (internalInnerMeasure_eq U hU (A + B) hCm)
  by_cases hne : MeasureNonextendible μ (internalInnerMeasure U hU) A B
  · by_cases hzeroA : μ p.left.active = 0
    · obtain ⟨K, hKm, hKpos, hcase⟩ := loeb_null_active_core_lift U hU q A B A' B' p
        hA'm hB'm hA'pos hB'pos hAA' hBB' hAmass hBmass hirr hfull (Or.inl hzeroA)
      exact hfinish K hKm hKpos hcase
    by_cases hzeroB : μ p.right.active = 0
    · obtain ⟨K, hKm, hKpos, hcase⟩ := loeb_null_active_core_lift U hU q A B A' B' p
        hA'm hB'm hA'pos hB'pos hAA' hBB' hAmass hBmass hirr hfull (Or.inr hzeroB)
      exact hfinish K hKm hKpos hcase
    obtain ⟨r, _, _, _⟩ := loeb_positive_quasiPeriodic_core_lift U hU q A B A' B' p
      hA'm hB'm hAA' hBB' hAmass hBmass (pos_iff_ne_zero.mpr hzeroA)
      (pos_iff_ne_zero.mpr hzeroB) hne hCm hperiod hfullCore
    exact Or.inr ⟨r⟩
  · unfold MeasureNonextendible at hne
    push_neg at hne
    obtain ⟨Ae, Be, hAem, hBem, hAAe, hBBe, hsame, hlarge⟩ := hne
    have hApos : 0 < μ A := by rwa [hAmass] at hA'pos
    have hBpos : 0 < μ B := by rwa [hBmass] at hB'pos
    have hsameMeasure : internalInnerMeasure U hU (Ae + Be) = μ (A + B) :=
      hsame.trans (internalInnerMeasure_eq U hU (A + B) hCm)
    obtain ⟨h, hperiodNat⟩ := extendible_equality_pair_has_essential_period U hU q A B Ae Be
      hAm hBm hCm hAem hBem hAAe hBBe hApos hBpos hcoreMeasure hlarge hsameMeasure
    exact hperiodic (naturalCyclicKernel U q h) (measurable_naturalCyclicKernel U q h)
      (naturalCyclicKernel_measure_pos U hU q h) hperiodNat

end Erdos335.Loeb

end
