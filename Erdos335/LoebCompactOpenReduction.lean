import Erdos335.LoebCompactDysonSequence
import Erdos335.LoebCompactSumTransfer
import Erdos335.CompactOpenMeasure

/-!
# A small open subgroup forces the quasi-periodic case

The shrinking sequence eventually puts its right input in one coset
of the subgroup. Recovery from that equality pair then gives a
quasi-periodic decomposition of the original inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance compactOpenReductionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_compact_small_open_subgroup_quasiPeriodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [PolishSpace K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableAdd₂ K] [MeasurableNeg K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set K) (hCsc : IsSigmaCompact C) (hDsc : IsSigmaCompact D)
    (hCpos : 0 < Measure.map φ (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map φ (loebMeasure U hU) D)
    (hcomp : 0 < loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D))ᶜ)
    (hfull : loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D)) =
      loebMeasure U hU (φ ⁻¹' C) + loebMeasure U hU (φ ⁻¹' D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ ((φ ⁻¹' C) + (φ ⁻¹' D)) =ᵐ[loebMeasure U hU]
        (φ ⁻¹' C) + (φ ⁻¹' D))
    (hperiod : ∀ z : K, z +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D → z = 0)
    (H : OpenAddSubgroup K)
    (hHsmall : Measure.map φ (loebMeasure U hU) (H : Set K) <
      Measure.map φ (loebMeasure U hU) (C + D)) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  let A := φ ⁻¹' C
  let B := φ ⁻¹' D
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure ν := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have hCm := measurableSet_of_sigmaCompact C hCsc
  have hDm := measurableSet_of_sigmaCompact D hDsc
  have hCDm := measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc)
  have hAm : MeasurableSet A := hCm.preimage hφ
  have hBm : MeasurableSet B := hDm.preimage hφ
  have hSm : MeasurableSet (A + B) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D]
    exact hCDm.preimage hφ
  have mass (S : Set K) (hS : MeasurableSet S) : μ (φ ⁻¹' S) = ν S :=
    (Measure.map_apply hφ hS).symm
  have hApos : 0 < μ A := (mass C hCm).symm ▸ hCpos
  have hBpos : 0 < μ B := (mass D hDm).symm ▸ hDpos
  have hSmass : μ (A + B) = ν (C + D) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D, mass (C + D) hCDm]
  rcases loeb_compact_dyson_sequence_or_quasiPeriodic U hU q φ hφ hsurj C D hCsc hDsc
    hCpos hDpos hcomp hfull hirr hne hnoAE with hp | hsequence
  · exact hp
  obtain ⟨Cn, Dn, en, hC0, hD0, hgood, hstep, _, hleftLimit⟩ := hsequence
  have hCn (n : ℕ) : MeasurableSet (Cn n) := measurableSet_of_sigmaCompact _ (hgood n).1
  have hDn (n : ℕ) : MeasurableSet (Dn n) := measurableSet_of_sigmaCompact _ (hgood n).2.1
  have hCDn (n : ℕ) : MeasurableSet (Cn n + Dn n) :=
    measurableSet_of_sigmaCompact _ (isSigmaCompact_add_sets _ _ (hgood n).1 (hgood n).2.1)
  have hsum (n : ℕ) : (φ ⁻¹' Cn n) + (φ ⁻¹' Dn n) =ᵐ[μ] φ ⁻¹' (C + D) := by
    rw [preimage_add_of_surjective_addHom φ hsurj C D]
    exact (hgood n).2.2.2.2
  have hlocal := compact_factor_shrinking_sumsets_localize U hU q φ hφ hsurj (C + D) hCDm
    hperiod Cn Dn hCDn hsum hleftLimit (H : Set K) (H.isOpen.mem_nhds H.zero_mem)
  obtain ⟨n, hn⟩ := hlocal.exists
  have hmassSum (k : ℕ) : ν (Cn k) + ν (Dn k) = ν C + ν D := by
    induction k with
    | zero => rw [hC0, hD0]
    | succ k ih =>
      rw [(hstep k).1, (hstep k).2.1, dysonGroup_measure_identity ν (Cn k) (Dn k) (hDn k) (en k)]
      exact ih
  let P := φ ⁻¹' Cn n
  let Q := φ ⁻¹' Dn n
  have hPm : MeasurableSet P := (hCn n).preimage hφ
  have hQm : MeasurableSet Q := (hDn n).preimage hφ
  have hPQm : MeasurableSet (P + Q) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj (Cn n) (Dn n)]
    exact (hCDn n).preimage hφ
  have hPpos : 0 < μ P := (mass (Cn n) (hCn n)).symm ▸ (hgood n).2.2.1
  have hQpos : 0 < μ Q := (mass (Dn n) (hDn n)).symm ▸ (hgood n).2.2.2.1
  have hPQae : P + Q =ᵐ[μ] A + B := (hgood n).2.2.2.2
  have hPQfull : μ (P + Q) = μ P + μ Q := by
    rw [measure_congr hPQae, hfull, mass C hCm, mass D hDm,
      mass (Cn n) (hCn n), mass (Dn n) (hDn n), hmassSum]
  rcases loeb_equal_sum_model_structure U hU q A B P Q hAm hBm hSm hApos hBpos hcomp hfull
    hirr hne hnoAE hPm hQm hPQm hPpos hQpos hPQfull hPQae with hp | hstructure
  · exact hp
  obtain ⟨hPQirr, hPQne, hPQnoAE⟩ := hstructure
  obtain ⟨d, hd⟩ := nonempty_of_measure_ne_zero ((hgood n).2.2.2.1).ne'
  obtain ⟨b, hb⟩ := hsurj d
  let L := H.toAddSubgroup.comap φ
  have hLm : MeasurableSet (L : Set G) := H.isOpen.measurableSet.preimage hφ
  have hQcoset : Q ⊆ b +ᵥ (L : Set G) := by
    intro x hx
    refine ⟨x - b, ?_, by simp [vadd_eq_add]⟩
    change φ (x - b) ∈ H
    rw [map_sub, hb]
    exact hn (sub_mem_sub hx hd)
  have hlarge : μ (L : Set G) < μ (Q + P) := by
    rw [add_comm Q P, measure_congr hPQae, hSmass]
    change μ (φ ⁻¹' (H : Set K)) < ν (C + D)
    rw [mass (H : Set K) H.isOpen.measurableSet]
    exact hHsmall
  have hnotperiod : ¬ ∃ J : AddSubgroup G, MeasurableSet (J : Set G) ∧
      0 < μ (J : Set G) ∧ (Q + P) + (J : Set G) =ᵐ[μ] Q + P := by
    rintro ⟨J, hJm, hJpos, hp⟩
    apply hPQnoAE J hJm hJpos
    intro t ht
    apply loeb_translate_ae_of_essential_period U hU q (P + Q) hPQm J _ t ht
    rw [add_comm P Q]
    exact ae_le_set.mp hp.le
  obtain ⟨p⟩ := loeb_quasiPeriodic_pair_of_one_coset_and_large_sum U hU q Q P L hLm b hQcoset
    hQm hPm (by simpa only [add_comm Q P] using hPQm) hQpos hPpos hlarge
    (by simpa only [add_comm] using hPQfull) hPQirr.swap hPQne.swap hnotperiod
  exact loeb_quasiPeriodic_pair_of_equal_sum_model U hU q A B P Q p.swap hPQm hPQae
    hAm hBm hSm hApos hBpos hcomp hfull hirr hne hnoAE

end Erdos335.Loeb

end
