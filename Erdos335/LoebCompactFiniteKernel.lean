import Erdos335.CompactFiniteCharacterKernel
import Erdos335.LoebCompactDysonSequence
import Erdos335.LoebCompactSumTransfer

/-!
# Finite character kernels in the connected aperiodic compact case
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance finiteKernelLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_compact_quasiPeriodic_or_finite_character_kernel
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [ConnectedSpace K] [T2Space K] [PolishSpace K]
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
    (χ : K →+ AddCircle (1 : ℝ)) (hχ : Continuous χ) (hχne : χ ≠ 0) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨ Finite χ.ker := by
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
  have hsumCompact (n : ℕ) : Cn n + Dn n ≤ᵐ[ν] C + D := by
    apply (ae_map_set_eq_of_preimage μ φ hφ (Cn n + Dn n) (C + D) (hCDn n) hSm ?_).le
    rw [preimage_add_of_surjective_addHom φ hsurj]
    exact hsum n
  have hmassSum (n : ℕ) : ν (Cn n) + ν (Dn n) = ν (C + D) := by
    induction n with
    | zero => rw [hC0, hD0, hstart]
    | succ n ih =>
      rw [(hstep n).1, (hstep n).2.1, dysonGroup_measure_identity ν (Cn n) (Dn n) (hDn n) (en n)]
      exact ih
  have hmassReal (n : ℕ) : (ν (C + D)).toReal = (ν (Cn n)).toReal + (ν (Dn n)).toReal := by
    rw [← hmassSum n, ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)]
  exact finite_character_kernel_of_localized_critical_pairs ν (C + D) hSm hperiod χ hχ hχne
    Cn Dn hDn (fun n => (hgood n).2.2.2.1) hsumCompact hmassReal
    (compact_factor_shrinking_sumsets_localize U hU q φ hφ hsurj (C + D) hSm hperiod
      Cn Dn hCDn hsum hleftLimit)

end Erdos335.Loeb

end
