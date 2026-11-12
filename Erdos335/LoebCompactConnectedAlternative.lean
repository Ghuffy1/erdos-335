import Erdos335.LoebCompactOpenReduction

/-!
# The open-connected-subgroup alternative for compact equality pairs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance compactConnectedAlternativeLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_compact_quasiPeriodic_or_open_connected
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
    (hperiod : ∀ z : K, z +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D → z = 0) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨ ∃ H : OpenAddSubgroup K, ConnectedSpace H := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure ν := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  rcases compact_open_subgroups_small_or_connected ν with hsmall | hconnected
  · have hCm := measurableSet_of_sigmaCompact C hCsc
    have hDm := measurableSet_of_sigmaCompact D hDsc
    have hCDm := measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc)
    have htotal : ν (C + D) = ν C + ν D := by
      rw [Measure.map_apply hφ hCDm, preimage_add_of_surjective_addHom φ hsurj, hfull,
        ← Measure.map_apply hφ hCm, ← Measure.map_apply hφ hDm]
    have hSpos : 0 < ν (C + D) := by
      rw [htotal]
      exact hCpos.trans_le le_self_add
    obtain ⟨H, _, hHsmall⟩ := hsmall (ν (C + D)) hSpos
    exact Or.inl (loeb_compact_small_open_subgroup_quasiPeriodic U hU q φ hφ hsurj C D
      hCsc hDsc hCpos hDpos hcomp hfull hirr hne hnoAE hperiod H hHsmall)
  · exact Or.inr hconnected

end Erdos335.Loeb

end
