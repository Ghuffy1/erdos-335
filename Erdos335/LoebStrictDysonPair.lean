import Erdos335.LoebQuasiPeriodicOutputRecovery
import Erdos335.LoebDysonPositiveOutput
import Erdos335.LoebQuasiPeriodicActiveBounds
import Erdos335.LoebEnvelopeStabilizer

/-!
# Pair recovery from a strict Dyson transform

For an irreducible nonextendible equality pair with aperiodic sum, a
strict transform with positive intersection produces a quasi-periodic
decomposition of the original pair. This is the zero-parameter case of
Griesmer's key lemma.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance strictDysonPairLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_strict_dyson_quasiPeriodic_pair
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hIpos : 0 < loebMeasure U hU (A ∩ B))
    (hCpos : 0 < loebMeasure U hU (A + B)ᶜ)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU ((A ∪ B) + (A ∩ B)) <
      loebMeasure U hU (A ∪ B) + loebMeasure U hU (A ∩ B))
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
  have hnotexact : ¬ ∃ K : AddSubgroup G, MeasurableSet (K : Set G) ∧
      0 < μ (K : Set G) ∧ (A + B) + (K : Set G) = A + B := by
    rintro ⟨K, hKm, hKpos, hp⟩
    apply hnoAE K hKm hKpos
    intro t ht
    have hfix : t +ᵥ (A + B) = A + B := subgroup_le_stabilizer_of_add_eq K (A + B) hp ht
    rw [hfix]
  let H := AddAction.stabilizer G ((A ∪ B) + (A ∩ B))
  have hApos : 0 < μ A := hIpos.trans_le (measure_mono inter_subset_left)
  have hBpos : 0 < μ B := hIpos.trans_le (measure_mono inter_subset_right)
  have hUpos : 0 < μ (A ∪ B) := hApos.trans_le (measure_mono subset_union_left)
  obtain ⟨_, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q (A ∪ B) (A ∩ B)
    (hAm.union hBm) (hAm.inter hBm) hUpos hIpos hsmall
  obtain ⟨D, p, _, hSD, _, hBgpos⟩ := loeb_strict_dyson_positive_background_model U hU q A B
    hAm hBm hSm hIpos hfull hsmall hnotexact
  have hActpos := (loeb_quasiPeriodic_active_mass_bounds U hU q (A + B) D H p hSD.symm
    (hnoAE H hHm hHpos)).1
  obtain ⟨b, hb⟩ := nonempty_of_measure_ne_zero hBgpos.ne'
  have hHbound : μ (H : Set G) ≤ μ p.background := by
    rw [← loeb_measure_section_eq_of_essential_period U hU H p.background
      p.background_measurable p.background_periodic b hb]
    exact measure_mono inter_subset_left
  have hparts : Disjoint p.background p.active := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp p.separated ⟨x, hy, 0, H.zero_mem, add_zero x⟩ hx
  have hDmass : μ D = μ p.background + μ p.active :=
    (congrArg μ p.partition).trans (measure_union hparts p.active_measurable)
  have hlarge : μ (H : Set G) < μ (A + B) := by
    rw [measure_congr hSD, hDmass]
    exact hHbound.trans_lt (ENNReal.lt_add_right (measure_ne_top μ _) hActpos.ne')
  exact loeb_quasiPeriodic_pair_of_large_output_model U hU q A B D H hHm hHpos p hSD.symm
    hAm hBm hSm hApos hBpos hCpos hlarge hfull hirr hne hnoAE

end Erdos335.Loeb

end
