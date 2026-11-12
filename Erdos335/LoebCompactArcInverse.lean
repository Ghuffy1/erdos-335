import Erdos335.LoebCompactCircleCosets
import Erdos335.LoebCircleCosetInverse

/-!
# Closed-arc alternatives for aperiodic compact equality models
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance compactArcInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_compact_quasiPeriodic_or_closedArc_cosets
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
    (hnoAE : ∀ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ L, t +ᵥ ((φ ⁻¹' C) + (φ ⁻¹' D)) =ᵐ[loebMeasure U hU]
        (φ ⁻¹' C) + (φ ⁻¹' D))
    (hperiod : ∀ z : K, z +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D → z = 0)
    (hcharacters : ∀ J : OpenAddSubgroup K, Nontrivial J →
      ∃ χ : J →+ AddCircle (1 : ℝ), Continuous χ ∧ χ ≠ 0) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨
      ∃ H : OpenAddSubgroup K, ConnectedSpace H ∧ ∃ u v : K,
        ∃ e : H ≃+ AddCircle (1 : ℝ), Continuous e ∧ Continuous e.symm ∧
        ∃ x y : AddCircle (1 : ℝ), ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b < 1 ∧
          C ⊆ u +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 a)))) ∧
          D ⊆ v +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b)))) ∧
          C =ᵐ[Measure.map φ (loebMeasure U hU)]
            u +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 a)))) ∧
          D =ᵐ[Measure.map φ (loebMeasure U hU)]
            v +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b)))) := by
  rcases loeb_compact_quasiPeriodic_or_circle_cosets U hU q φ hφ hsurj C D hCsc hDsc
    hCpos hDpos hcomp hfull hirr hne hnoAE hperiod hcharacters with hQP | hcosets
  · exact Or.inl hQP
  obtain ⟨H, hconnected, u, v, hCH, hDH, e, he, hesymm⟩ := hcosets
  obtain ⟨x, y, a, b, ha, hb, hab, hCsub, hDsub, hCae, hDae⟩ :=
    loeb_circle_coset_inverse U hU q φ hφ hsurj C D
      (measurableSet_of_sigmaCompact C hCsc) (measurableSet_of_sigmaCompact D hDsc)
      (measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc))
      hCpos hDpos hfull hirr hne hnoAE hperiod H u v hCH hDH e he hesymm
  exact Or.inr ⟨H, hconnected, u, v, e, he, hesymm, x, y, a, b, ha, hb, hab,
    hCsub, hDsub, hCae, hDae⟩

end Erdos335.Loeb

end
