import Erdos335.CompactCosetCharacterKernel
import Erdos335.ConnectedCircleClassification
import Erdos335.CompactDysonCosetPreservation
import Erdos335.LoebCompactDysonSequence
import Erdos335.LoebCompactSumTransfer

/-!
# Circle models on connected open cosets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance cosetCircleLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_compact_quasiPeriodic_or_coset_circle_model
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
    (H : OpenAddSubgroup K) [ConnectedSpace H]
    (a b : K) (hCH : C ⊆ a +ᵥ (H : Set K)) (hDH : D ⊆ b +ᵥ (H : Set K))
    (χ : H →+ AddCircle (1 : ℝ)) (hχ : Continuous χ) (hχne : χ ≠ 0) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨ ∃ e : H ≃+ AddCircle (1 : ℝ), Continuous e ∧ Continuous e.symm := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : ν.IsAddHaarMeasure := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have hCm := measurableSet_of_sigmaCompact C hCsc
  have hDm := measurableSet_of_sigmaCompact D hDsc
  have hSm := measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc)
  have mass (S : Set K) (hS : MeasurableSet S) : μ (φ ⁻¹' S) = ν S :=
    (Measure.map_apply hφ hS).symm
  have hstart : ν (C + D) = ν C + ν D := by
    rw [← mass (C + D) hSm, preimage_add_of_surjective_addHom φ hsurj,
      hfull, mass C hCm, mass D hDm]
  rcases loeb_compact_dyson_sequence_or_quasiPeriodic U hU q φ hφ hsurj C D hCsc hDsc
    hCpos hDpos hcomp hfull hirr hne hnoAE with hp | hsequence
  · exact Or.inl hp
  right
  obtain ⟨Cn, Dn, en, hC0, hD0, hgood, hstep, _, hleftLimit⟩ := hsequence
  have hCn (n : ℕ) : MeasurableSet (Cn n) := measurableSet_of_sigmaCompact _ (hgood n).1
  have hDn (n : ℕ) : MeasurableSet (Dn n) := measurableSet_of_sigmaCompact _ (hgood n).2.1
  have hCDn (n : ℕ) : MeasurableSet (Cn n + Dn n) :=
    measurableSet_of_sigmaCompact _ (isSigmaCompact_add_sets _ _ (hgood n).1 (hgood n).2.1)
  have hsum (n : ℕ) : (φ ⁻¹' Cn n) + (φ ⁻¹' Dn n) =ᵐ[μ] φ ⁻¹' (C + D) := by
    rw [preimage_add_of_surjective_addHom φ hsurj C D]
    exact (hgood n).2.2.2.2
  have hsumCompact (n : ℕ) : Cn n + Dn n =ᵐ[ν] C + D := by
    apply ae_map_set_eq_of_preimage μ φ hφ (Cn n + Dn n) (C + D) (hCDn n) hSm
    rw [preimage_add_of_surjective_addHom φ hsurj]
    exact hsum n
  have hmassSum (n : ℕ) : ν (Cn n) + ν (Dn n) = ν (C + D) := by
    induction n with
    | zero => rw [hC0, hD0, hstart]
    | succ n ih =>
      rw [(hstep n).1, (hstep n).2.1, dysonGroup_measure_identity ν (Cn n) (Dn n) (hDn n) (en n)]
      exact ih
  have hcosets := dyson_chain_preserves_cosets H.toAddSubgroup Cn Dn en a b
    (by change Cn 0 ⊆ a +ᵥ (H : Set K); simpa only [hC0] using hCH)
    (by change Dn 0 ⊆ b +ᵥ (H : Set K); simpa only [hD0] using hDH)
    (fun n => (hstep n).1) (fun n => (hstep n).2.1)
    (fun n => nonempty_of_measure_ne_zero ((hgood n).2.2.2.1).ne')
  have hCnH (n : ℕ) : Cn n ⊆ a +ᵥ (H : Set K) := (hcosets n).1
  have hDnH (n : ℕ) : Dn n ⊆ b +ᵥ (H : Set K) := (hcosets n).2
  have hSH : C + D ⊆ (a + b) +ᵥ (H : Set K) := by
    rintro z ⟨c, hc, d, hd, rfl⟩
    obtain ⟨h, hh, hhc⟩ := hCH hc
    obtain ⟨k, hk, hkd⟩ := hDH hd
    refine ⟨h + k, H.add_mem hh hk, ?_⟩
    change a + h = c at hhc
    change b + k = d at hkd
    change (a + b) + (h + k) = c + d
    rw [← hhc, ← hkd]
    abel
  have hkernel : Finite χ.ker := finite_character_kernel_on_connected_cosets ν H a b
    (C + D) hSm hSH hperiod Cn Dn hCnH hDnH hDn (fun n => (hgood n).2.2.2.1)
    hsumCompact (fun n => (hmassSum n).symm)
    (compact_factor_shrinking_sumsets_localize U hU q φ hφ hsurj (C + D) hSm hperiod
      Cn Dn hCDn hsum hleftLimit) χ hχ hχne
  have : Finite χ.ker := hkernel
  have : IsTopologicalAddGroup H := inferInstanceAs (IsTopologicalAddGroup H.toAddSubgroup)
  have : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  exact exists_circle_addEquiv_of_finite_character_kernel χ hχ hχne

end Erdos335.Loeb

end
