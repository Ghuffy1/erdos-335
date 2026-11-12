import Erdos335.CircleArcClassification
import Erdos335.LoebCompactDysonSequence
import Erdos335.LoebCompactSumTransfer
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Arc structure for an aperiodic circle factor of a critical Loeb pair
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance circleSumArcLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_unitCircle_sum_ae_arc_or_quasiPeriodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ))) (hCsc : IsSigmaCompact C) (hDsc : IsSigmaCompact D)
    (hCpos : 0 < volume C) (hDpos : 0 < volume D)
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
    (hperiod : ∀ z : AddCircle (1 : ℝ), z +ᵥ (C + D) =ᵐ[volume] C + D → z = 0) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨
    ∃ c a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ b - a < 1 ∧
      (-(c : AddCircle (1 : ℝ)) +ᵥ (C + D)) =ᵐ[volume]
        (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  have : IsProbabilityMeasure (Measure.map φ μ) := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure (Measure.map φ μ) :=
    loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have hvolume : Measure.map φ μ = volume :=
    Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  have hvolume' : Measure.map φ (loebMeasure U hU) = volume := hvolume
  have : (volume : Measure (AddCircle (1 : ℝ))).IsNegInvariant := by
    rw [← hvolume']
    exact loebMeasure_map_hom_isNegInvariant U hU q φ hφ
  have mass (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S) :
      μ (φ ⁻¹' S) = volume S := by
    rw [← Measure.map_apply hφ hS, hvolume]
  have hCm := measurableSet_of_sigmaCompact C hCsc
  have hDm := measurableSet_of_sigmaCompact D hDsc
  have hSm := measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc)
  have hfullK : volume (C + D) = volume C + volume D := by
    rw [← mass (C + D) hSm, preimage_add_of_surjective_addHom φ hsurj C D,
      hfull, mass C hCm, mass D hDm]
  have hSpos : 0 < volume (C + D) := by
    rw [hfullK]
    exact add_pos_of_pos_of_nonneg hCpos bot_le
  have hScomp : 0 < volume (C + D)ᶜ := by
    rw [← mass (C + D)ᶜ hSm.compl, preimage_compl,
      preimage_add_of_surjective_addHom φ hsurj C D]
    exact hcomp
  have hCpos' : 0 < Measure.map φ (loebMeasure U hU) C := by
    change 0 < Measure.map φ μ C
    rwa [hvolume]
  have hDpos' : 0 < Measure.map φ (loebMeasure U hU) D := by
    change 0 < Measure.map φ μ D
    rwa [hvolume]
  rcases loeb_compact_dyson_sequence_or_quasiPeriodic U hU q φ hφ hsurj C D hCsc hDsc
    hCpos' hDpos' hcomp hfull hirr hne hnoAE with hp | hsequence
  · exact Or.inl hp
  right
  obtain ⟨Cn, Dn, en, hC0, hD0, hgood, hstep, _, hleftLimit⟩ := hsequence
  have hCn (n : ℕ) : MeasurableSet (Cn n) := measurableSet_of_sigmaCompact _ (hgood n).1
  have hDn (n : ℕ) : MeasurableSet (Dn n) := measurableSet_of_sigmaCompact _ (hgood n).2.1
  have hCDn (n : ℕ) : MeasurableSet (Cn n + Dn n) :=
    measurableSet_of_sigmaCompact _ (isSigmaCompact_add_sets _ _ (hgood n).1 (hgood n).2.1)
  have hsum (n : ℕ) : Cn n + Dn n =ᵐ[volume] C + D := by
    have hpre := (hgood n).2.2.2.2
    rw [← preimage_add_of_surjective_addHom φ hsurj (Cn n) (Dn n),
      ← preimage_add_of_surjective_addHom φ hsurj C D] at hpre
    have h := ae_map_set_eq_of_preimage μ φ hφ _ _ (hCDn n) hSm hpre
    rwa [hvolume] at h
  have hmassSum (n : ℕ) : volume (Cn n) + volume (Dn n) = volume C + volume D := by
    induction n with
    | zero => rw [hC0, hD0]
    | succ n ih =>
      rw [(hstep n).1, (hstep n).2.1,
        dysonGroup_measure_identity volume (Cn n) (Dn n) (hDn n) (en n)]
      exact ih
  have hmass (n : ℕ) : (volume (C + D)).toReal =
      (volume (Cn n)).toReal + (volume (Dn n)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top volume _) (measure_ne_top volume _),
      hmassSum, ← hfullK]
  have hDpositive (n : ℕ) : 0 < volume (Dn n) := by
    simpa only [hvolume'] using (hgood n).2.2.2.1
  have hleft : Tendsto (fun n => (volume (Cn n)).toReal) atTop (𝓝 (volume (C + D)).toReal) := by
    simpa only [hvolume'] using hleftLimit
  have hlocal : ∀ V ∈ 𝓝 (0 : AddCircle (1 : ℝ)), ∀ᶠ n in atTop, Dn n - Dn n ⊆ V := by
    intro V hV
    exact shrinking_sumsets_localize volume (C + D) hSm hperiod Cn Dn
      (fun n => (hsum n).le) hleft V hV
  exact unitCircle_ae_arc_of_localized_critical_pairs (C + D) hSm hSpos hScomp Cn Dn
    hDn hDpositive (fun n => (hsum n).le) hmass hlocal

end Erdos335.Loeb

end
