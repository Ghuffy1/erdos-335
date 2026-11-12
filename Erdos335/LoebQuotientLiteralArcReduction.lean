import Erdos335.LoebCompactQuotientPair
import Erdos335.LoebAEModelStructure
import Erdos335.LoebQuotientArcReduction
import Erdos335.LoebOpenArcModelContainment

/-!
# Literal Loeb containment from an aperiodic compact quotient
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quotientLiteralArcLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quotient_quasiPeriodic_or_literal_closedArc_cosets
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K L : Type*} [AddCommGroup K] [AddCommGroup L]
    [TopologicalSpace K] [TopologicalSpace L] [IsTopologicalAddGroup K]
    [IsTopologicalAddGroup L] [CompactSpace K] [CompactSpace L]
    [T2Space K] [T2Space L] [PolishSpace K] [PolishSpace L]
    [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
    [MeasurableAdd₂ K] [MeasurableNeg K] [MeasurableAdd₂ L] [MeasurableNeg L]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (ψ : K →+ L) (hψ : Continuous ψ) (hψsurj : Function.Surjective ψ)
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
    (hker : ∀ t : K, t ∈ ψ.ker ↔
      t +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D)
    (hcharacters : ∀ J : OpenAddSubgroup L, Nontrivial J →
      ∃ χ : J →+ AddCircle (1 : ℝ), Continuous χ ∧ χ ≠ 0) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨
      ∃ H : OpenAddSubgroup L, ConnectedSpace H ∧ ∃ u v : L,
        ∃ e : H ≃+ AddCircle (1 : ℝ), Continuous e ∧ Continuous e.symm ∧
        ∃ x y : AddCircle (1 : ℝ), ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b < 1 ∧
          (φ ⁻¹' C) ⊆ (ψ.comp φ) ⁻¹'
            (u +ᵥ ((Subtype.val : H → L) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 a))))) ∧
          (φ ⁻¹' D) ⊆ (ψ.comp φ) ⁻¹'
            (v +ᵥ ((Subtype.val : H → L) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b))))) ∧
          (φ ⁻¹' C) =ᵐ[loebMeasure U hU] (ψ.comp φ) ⁻¹'
            (u +ᵥ ((Subtype.val : H → L) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 a))))) ∧
          (φ ⁻¹' D) =ᵐ[loebMeasure U hU] (ψ.comp φ) ⁻¹'
            (v +ᵥ ((Subtype.val : H → L) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b))))) := by
  rcases loeb_quotient_quasiPeriodic_or_closedArc_cosets U hU q φ hφ hsurj ψ hψ hψsurj
    C D hCsc hDsc hCpos hDpos hcomp hfull hirr hne hnoAE hker hcharacters with hQP | hmodel
  · exact Or.inl hQP
  obtain ⟨P, Q, hPsc, hQsc, hPA, hQB, hPQ, hperiod,
    H, hconnected, u, v, e, he, hesymm, x, y, a, b, ha, hb, hab, hPsub, hQsub, hPae, hQae⟩ := hmodel
  let θ := ψ.comp φ
  have hθ : Measurable θ := hψ.measurable.comp hφ
  have hθsurj : Function.Surjective θ := hψsurj.comp hsurj
  let I := u +ᵥ ((Subtype.val : H → L) ''
    (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 a))))
  let J := v +ᵥ ((Subtype.val : H → L) ''
    (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b))))
  have hAmodel : (φ ⁻¹' C) =ᵐ[loebMeasure U hU] θ ⁻¹' I := by
    have h := ae_of_ae_map hθ.aemeasurable hPae
    exact hPA.symm.trans h
  have hBmodel : (φ ⁻¹' D) =ᵐ[loebMeasure U hU] θ ⁻¹' J := by
    have h := ae_of_ae_map hθ.aemeasurable hQae
    exact hQB.symm.trans h
  have hCm := measurableSet_of_sigmaCompact C hCsc
  have hDm := measurableSet_of_sigmaCompact D hDsc
  have hSm := measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc)
  have hSpre : MeasurableSet ((φ ⁻¹' C) + (φ ⁻¹' D)) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj]
    exact hSm.preimage hφ
  obtain ⟨hAsub, hBsub⟩ := loeb_open_circle_model_literal_containment U hU q θ hθ hθsurj
    (φ ⁻¹' C) (φ ⁻¹' D) (hCm.preimage hφ) (hDm.preimage hφ) hSpre hirr
    H e he hesymm u v x y a b ha hb hab hAmodel hBmodel
  exact Or.inr ⟨H, hconnected, u, v, e, he, hesymm, x, y, a, b, ha, hb, hab,
    hAsub, hBsub, hAmodel, hBmodel⟩

end Erdos335.Loeb

end
