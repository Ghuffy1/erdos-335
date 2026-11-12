import Erdos335.LoebAperiodicRestriction
import Erdos335.LoebOneCosetPair
import Erdos335.LoebQuasiPeriodicCoreLift

/-!
# Recovering a pair from a full-measure quasi-periodic partner

A positive background gives pair recovery directly. If the background
is null, irreducibility permits restriction to the active coset. The
sum's measure exceeding that coset then gives pair recovery as well.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicPartnerLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_pair_of_full_measure_partner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H D)
    (hDB : D ⊆ B) (hDmass : loebMeasure U hU D = loebMeasure U hU B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hlarge : loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) < loebMeasure U hU (A + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) →
      ¬ ∀ t ∈ K, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have finish (Q : Set G) (hQB : Q ⊆ B) (hQmass : μ Q = μ B)
      (hAQm : MeasurableSet (A + Q))
      (r : QuasiPeriodicPairData μ (internalInnerMeasure U hU) A Q) :
      Nonempty (QuasiPeriodicPairData μ (internalInnerMeasure U hU) A B) := by
    have h := loeb_irreducible_extension_of_quasiPeriodic_core U hU q A Q A B r
      hAm hBm hApos hBpos Subset.rfl hQB rfl hQmass.symm hirr hAQm
      ((internalInnerMeasure_eq U hU _ hSm).trans hfull)
    rcases h with ⟨K, hKm, hKpos, hp⟩ | hr
    · apply False.elim
      apply hnoAE K hKm hKpos
      intro t ht
      exact loeb_translate_ae_of_essential_period U hU q (A + B) hSm K
        (ae_le_set.mp hp.le) t ht
    · exact hr
  have no_saturation (S : Set G) (hS : MeasurableSet S)
      (hp : ∀ K : AddSubgroup G, MeasurableSet (K : Set G) → 0 < μ (K : Set G) →
        ¬ ∀ t ∈ K, t +ᵥ S =ᵐ[μ] S) :
      ¬ ∃ K : AddSubgroup G, MeasurableSet (K : Set G) ∧ 0 < μ (K : Set G) ∧ S + (K : Set G) =ᵐ[μ] S := by
    rintro ⟨K, hKm, hKpos, hperiod⟩
    apply hp K hKm hKpos
    intro t ht
    exact loeb_translate_ae_of_essential_period U hU q S hS K (ae_le_set.mp hperiod.le) t ht
  have hDm : MeasurableSet D := p.partition.symm ▸ (p.background_measurable.union p.active_measurable)
  have hDpos : 0 < μ D := hDmass.symm ▸ hBpos
  by_cases hBgpos : 0 < μ p.background
  · obtain ⟨hADm, _, hADfull, hADirr, hADne, hADnoAE⟩ := loeb_aperiodic_full_measure_restriction U hU q
      A B A D hAm hDm hSm hApos hDpos Subset.rfl hDB rfl hDmass hirr hfull hnoAE
    have hDAnoAE : ∀ K : AddSubgroup G, MeasurableSet (K : Set G) → 0 < μ (K : Set G) →
        ¬ ∀ t ∈ K, t +ᵥ (D + A) =ᵐ[μ] D + A := by
      simpa only [add_comm D A] using hADnoAE
    have hDAm : MeasurableSet (D + A) := by simpa only [add_comm D A] using hADm
    obtain ⟨r⟩ := loeb_quasiPeriodic_pair_of_nonnull_background U hU q D A H hHm hHpos p
      hAm hDAm hBgpos hDpos hApos (by simpa only [add_comm] using hADfull)
      hADirr.swap hADne.swap (no_saturation (D + A) hDAm hDAnoAE)
    exact finish D hDB hDmass hADm r.swap
  have hBgzero : μ p.background = 0 := le_antisymm (not_lt.mp hBgpos) bot_le
  let Q := p.active
  have hQD : Q ⊆ D := subset_union_right.trans p.partition.ge
  have hQB : Q ⊆ B := hQD.trans hDB
  have hQmass : μ Q = μ B := by
    have hparts : Disjoint p.background p.active := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp p.separated ⟨x, hy, 0, H.zero_mem, add_zero x⟩ hx
    have h := (congrArg μ p.partition).trans (measure_union hparts p.active_measurable)
    rw [hBgzero, zero_add] at h
    exact h.symm.trans hDmass
  have hQpos : 0 < μ Q := hQmass.symm ▸ hBpos
  obtain ⟨hAQm, hAQae, hAQfull, hAQirr, hAQne, hAQnoAE⟩ := loeb_aperiodic_full_measure_restriction U hU q
    A B A Q hAm p.active_measurable hSm hApos hQpos Subset.rfl hQB rfl hQmass hirr hfull hnoAE
  have hQAm : MeasurableSet (Q + A) := by simpa only [add_comm Q A] using hAQm
  have hQAnoAE : ∀ K : AddSubgroup G, MeasurableSet (K : Set G) → 0 < μ (K : Set G) →
      ¬ ∀ t ∈ K, t +ᵥ (Q + A) =ᵐ[μ] Q + A := by
    simpa only [add_comm Q A] using hAQnoAE
  have hQAfull : μ (Q + A) = μ Q + μ A := by simpa only [add_comm] using hAQfull
  have hQAlarge : μ (H : Set G) < μ (Q + A) := by
    rw [add_comm Q A, measure_congr hAQae]
    exact hlarge
  obtain ⟨r⟩ := loeb_quasiPeriodic_pair_of_one_coset_and_large_sum U hU q Q A H hHm p.anchor
    p.active_subset_coset p.active_measurable hAm hQAm hQpos hApos hQAlarge hQAfull
    hAQirr.swap hAQne.swap (no_saturation (Q + A) hQAm hQAnoAE)
  exact finish Q hQB hQmass hAQm r.swap

end Erdos335.Loeb

end
