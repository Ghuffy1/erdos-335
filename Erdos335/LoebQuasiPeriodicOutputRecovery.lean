import Erdos335.LoebNegativePartner
import Erdos335.LoebPositiveQuasiPeriodic
import Erdos335.LoebQuasiPeriodicActivePositive
import Erdos335.LoebQuasiPeriodicActiveStructure
import Erdos335.LoebQuasiPeriodicComplement
import Erdos335.LoebQuasiPeriodicActiveBounds
import Erdos335.LoebComplementStructure

/-!
# Recovering the input pair from a quasi-periodic output

The output has measure greater than its active coset. Complement duality
then produces a quasi-periodic partner. Retaining the active piece when
the background period is enlarged permits a second one-coset reduction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicOutputRecoveryLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_pair_of_large_output_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H D)
    (hDS : D =ᵐ[loebMeasure U hU] A + B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hCpos : 0 < loebMeasure U hU (A + B)ᶜ)
    (hlarge : loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) < loebMeasure U hU (A + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) →
      ¬ ∀ t ∈ K, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let C := (A + B)ᶜ
  have hnegBm : MeasurableSet (-B) := hBm.preimage (measurable_loeb_neg U hU)
  have hnegBpos : 0 < μ (-B) := by rwa [loebMeasure_neg U hU B hBm]
  have no_saturation (S : Set G) (hS : MeasurableSet S)
      (hp : ∀ K : AddSubgroup G, MeasurableSet (K : Set G) → 0 < μ (K : Set G) →
        ¬ ∀ t ∈ K, t +ᵥ S =ᵐ[μ] S) :
      ¬ ∃ K : AddSubgroup G, MeasurableSet (K : Set G) ∧ 0 < μ (K : Set G) ∧ S + (K : Set G) =ᵐ[μ] S := by
    rintro ⟨K, hKm, hKpos, hperiod⟩
    apply hp K hKm hKpos
    intro t ht
    exact loeb_translate_ae_of_essential_period U hU q S hS K (ae_le_set.mp hperiod.le) t ht
  have complete (P Q : Set G) (hPm : MeasurableSet P) (hQm : MeasurableSet Q)
      (hPQm : MeasurableSet (P + Q)) (hPpos : 0 < μ P)
      (a : G) (hPcoset : P ⊆ a +ᵥ (H : Set G))
      (hPQfull : μ (P + Q) = μ P + μ Q)
      (hPQnoAE : ∀ K : AddSubgroup G, MeasurableSet (K : Set G) → 0 < μ (K : Set G) →
        ¬ ∀ t ∈ K, t +ᵥ (P + Q) =ᵐ[μ] P + Q)
      (hQB : Q ⊆ -B) (hQmass : μ Q = μ (-B)) :
      Nonempty (QuasiPeriodicPairData μ (internalInnerMeasure U hU) A B) := by
    have hnotexact : ¬ ∃ K : AddSubgroup G, MeasurableSet (K : Set G) ∧
        0 < μ (K : Set G) ∧ (P + Q) + (K : Set G) = P + Q := by
      rintro ⟨K, hKm, hKpos, hp⟩
      apply no_saturation (P + Q) hPQm hPQnoAE
      refine ⟨K, hKm, hKpos, ?_⟩
      rw [hp]
    obtain ⟨K, hKm, hKpos, hKH, ⟨r⟩⟩ := loeb_one_coset_input_reduction U hU q
      P Q H a hPcoset hPm hQm hPQm hPpos hPQfull hnotexact
    have hKlarge : μ (K : Set G) < μ (A + B) := (measure_mono hKH).trans_lt hlarge
    exact loeb_pair_of_negative_full_measure_partner U hU q A B Q K hKm hKpos r hQB hQmass
      hAm hBm hSm hApos hBpos hKlarge hfull hirr hnoAE
  obtain ⟨hEm, _, hdual⟩ := loeb_nonextendible_complement_duality U hU q A B
    hAm hBm hSm hBpos hCpos hfull hne
  have hdualFull : μ ((-B) + C) = μ (-B) + μ C :=
    (internalInnerMeasure_eq U hU _ hEm).symm.trans hdual
  obtain ⟨hdualIrr, _, hdualNoAE⟩ := loeb_complement_dual_structure U hU q A B
    hAm hBm hSm hApos hBpos hCpos hfull hirr hne hnoAE
  have hpartial := (loeb_quasiPeriodic_active_mass_bounds U hU q (A + B) D H p hDS
    (hnoAE H hHm hHpos)).2
  obtain ⟨C₀, hC₀C, hC₀ae, r, hrpos⟩ := loeb_quasiPeriodic_complement_core U hU q
    (A + B) D hSm H hHm hHpos p hDS hpartial
  have hC₀m : MeasurableSet C₀ := r.partition.symm ▸ (r.background_measurable.union r.active_measurable)
  have hC₀mass : μ C₀ = μ C := measure_congr hC₀ae
  have hC₀pos : 0 < μ C₀ := hC₀mass.symm ▸ hCpos
  obtain ⟨hE₀m, _, hE₀full, hE₀irr, hE₀ne, hE₀noAE⟩ := loeb_aperiodic_full_measure_restriction U hU q
    (-B) C (-B) C₀ hnegBm hC₀m hEm hnegBpos hC₀pos Subset.rfl hC₀C rfl hC₀mass
    hdualIrr hdualFull hdualNoAE
  have hC₀Bm : MeasurableSet (C₀ + (-B)) := by simpa only [add_comm C₀ (-B)] using hE₀m
  have hC₀Bfull : μ (C₀ + (-B)) = μ C₀ + μ (-B) := by simpa only [add_comm] using hE₀full
  have hC₀BnoAE : ∀ K : AddSubgroup G, MeasurableSet (K : Set G) → 0 < μ (K : Set G) →
      ¬ ∀ t ∈ K, t +ᵥ (C₀ + (-B)) =ᵐ[μ] C₀ + (-B) := by
    simpa only [add_comm C₀ (-B)] using hE₀noAE
  by_cases hBgpos : 0 < μ r.background
  · obtain ⟨s, _, hsAct, _⟩ := loeb_quasiPeriodic_pair_of_positive_background_data U hU q C₀ (-B)
      H hHm hHpos r hnegBm hC₀Bm hBgpos hrpos hnegBpos hC₀Bfull hE₀irr.swap hE₀ne.swap
      (no_saturation (C₀ + (-B)) hC₀Bm hC₀BnoAE)
    by_cases hsBgpos : 0 < μ s.right.background
    · exact loeb_pair_of_negative_positive_background U hU q A B s.period s.period_measurable
        s.period_positive s.right hsBgpos hAm hBm hSm hApos hBpos hfull hirr hne hnoAE
    have hsBgzero : μ s.right.background = 0 := le_antisymm (not_lt.mp hsBgpos) bot_le
    have hsLeftPos : 0 < μ s.left.active := hsAct.symm ▸ hrpos
    have hsRightPos : 0 < μ s.right.active := loeb_quasiPeriodic_active_positive_of_irreducible U hU q
      (-B) C₀ s.period s.period_measurable s.period_positive s.right hC₀m hE₀m hE₀irr
      (hE₀noAE s.period s.period_measurable s.period_positive)
    obtain ⟨hActm, _, _, hActNoAE⟩ := loeb_quasiPeriodic_active_structure U hU q C₀ (-B) s
      hC₀Bm hsLeftPos hsRightPos hE₀irr.swap hC₀BnoAE
    have hActFull : μ (s.left.active + s.right.active) = μ s.left.active + μ s.right.active :=
      (internalInnerMeasure_eq U hU _ hActm).symm.trans s.active_identity
    have hRightMass : μ s.right.active = μ (-B) := by
      have hparts : Disjoint s.right.background s.right.active := by
        apply Set.disjoint_left.mpr
        intro x hx hy
        exact Set.disjoint_left.mp s.right.separated ⟨x, hy, 0, s.period.zero_mem, add_zero x⟩ hx
      have h := (congrArg μ s.right.partition).trans (measure_union hparts s.right.active_measurable)
      rw [hsBgzero, zero_add] at h
      exact h.symm
    have hActCoset : s.left.active ⊆ r.anchor +ᵥ (H : Set G) := by
      rw [hsAct]
      exact r.active_subset_coset
    exact complete s.left.active s.right.active s.left.active_measurable s.right.active_measurable
      hActm hsLeftPos r.anchor hActCoset hActFull hActNoAE
      (subset_union_right.trans s.right.partition.ge) hRightMass
  have hBgzero : μ r.background = 0 := le_antisymm (not_lt.mp hBgpos) bot_le
  have hActMass : μ r.active = μ C := by
    have hparts : Disjoint r.background r.active := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp r.separated ⟨x, hy, 0, H.zero_mem, add_zero x⟩ hx
    have h := (congrArg μ r.partition).trans (measure_union hparts r.active_measurable)
    rw [hBgzero, zero_add] at h
    exact h.symm.trans hC₀mass
  have hActC : r.active ⊆ C := (subset_union_right.trans r.partition.ge).trans hC₀C
  obtain ⟨hE₁m, _, hE₁full, _, _, hE₁noAE⟩ := loeb_aperiodic_full_measure_restriction U hU q
    (-B) C (-B) r.active hnegBm r.active_measurable hEm hnegBpos hrpos Subset.rfl hActC rfl hActMass
    hdualIrr hdualFull hdualNoAE
  apply complete r.active (-B) r.active_measurable hnegBm
    (by simpa only [add_comm r.active (-B)] using hE₁m) hrpos r.anchor r.active_subset_coset
    (by simpa only [add_comm] using hE₁full)
    (by simpa only [add_comm r.active (-B)] using hE₁noAE) Subset.rfl rfl

end Erdos335.Loeb

end
