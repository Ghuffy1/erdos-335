import Erdos335.LoebCompactCircleCosets
import Erdos335.LoebQuotientSubgroupCharacter

/-!
# Circle cosets in an essential-stabilizer quotient
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quotientCircleCosetsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U
local instance quotientCircleCosetsCircleSpace : MeasurableSpace (Additive Circle) :=
    borel (Additive Circle)
local instance quotientCircleCosetsCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
variable (F : ℕ → ∀ n, ZMod (q n : ℕ) →+ Additive Circle)
variable [CompactSpace (countableUltralimitHom U F).range]


variable (H : AddSubgroup (countableUltralimitHom U F).range)


variable [T2Space ((countableUltralimitHom U F).range ⧸ H)] [PolishSpace ((countableUltralimitHom U F).range ⧸ H)] [MeasurableSpace ((countableUltralimitHom U F).range ⧸ H)] [BorelSpace ((countableUltralimitHom U F).range ⧸ H)]
variable [MeasurableAdd₂ ((countableUltralimitHom U F).range ⧸ H)] [MeasurableNeg ((countableUltralimitHom U F).range ⧸ H)]

theorem loeb_essential_quotient_quasiPeriodic_or_circle_cosets
    (S : Set (countableUltralimitHom U F).range) (hS : MeasurableSet S)
    (hH : ∀ s, s ∈ H ↔
      s +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)] S)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ ((countableUltralimitHom U F).range ⧸ H))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set ((countableUltralimitHom U F).range ⧸ H)) (hCsc : IsSigmaCompact C) (hDsc : IsSigmaCompact D)
    (hCpos : 0 < Measure.map φ (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map φ (loebMeasure U hU) D)
    (hcomp : 0 < loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D))ᶜ)
    (hfull : loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D)) =
      loebMeasure U hU (φ ⁻¹' C) + loebMeasure U hU (φ ⁻¹' D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hnoAE : ∀ J : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (J : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (J : Set _) →
      ¬ ∀ t ∈ J, t +ᵥ ((φ ⁻¹' C) + (φ ⁻¹' D)) =ᵐ[loebMeasure U hU]
        (φ ⁻¹' C) + (φ ⁻¹' D))
    (hperiod : ∀ z : ((countableUltralimitHom U F).range ⧸ H), z +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D → z = 0) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨
      ∃ J : OpenAddSubgroup ((countableUltralimitHom U F).range ⧸ H), ConnectedSpace J ∧ ∃ a b : ((countableUltralimitHom U F).range ⧸ H),
        C ⊆ a +ᵥ (J : Set ((countableUltralimitHom U F).range ⧸ H)) ∧ D ⊆ b +ᵥ (J : Set ((countableUltralimitHom U F).range ⧸ H)) ∧
        ∃ e : J ≃+ AddCircle (1 : ℝ), Continuous e ∧ Continuous e.symm := by
  apply loeb_compact_quasiPeriodic_or_circle_cosets U hU q φ hφ hsurj C D hCsc hDsc
    hCpos hDpos hcomp hfull hirr hne hnoAE hperiod
  intro J hJ
  have : Nontrivial J.toAddSubgroup := hJ
  exact exists_nontrivial_character_on_quotient_subgroup U hU F S hS H hH J.toAddSubgroup

end Erdos335.Loeb

end
