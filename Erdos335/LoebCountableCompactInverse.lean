import Erdos335.LoebQuotientLiteralArcReduction
import Erdos335.LoebQuotientSubgroupCharacter
import Erdos335.EssentialStabilizerQuotientTopology
import Erdos335.LoebBohrPairFromCompactCosets

/-!
# Internal Bohr alternatives for countable compact equality models
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance countableInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U
local instance countableInverseCircleSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance countableInverseCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem loeb_countable_compact_quasiPeriodic_or_internalBohr
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (F : ℕ → ∀ n, ZMod (q n : ℕ) →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (C D : Set (countableUltralimitHom U F).range) (hCsc : IsSigmaCompact C) (hDsc : IsSigmaCompact D)
    (hCpos : 0 < Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) D)
    (hcomp : 0 < loebMeasure U hU
      (((countableUltralimitHom U F).rangeRestrict ⁻¹' C) +
        ((countableUltralimitHom U F).rangeRestrict ⁻¹' D))ᶜ)
    (hfull : loebMeasure U hU
        (((countableUltralimitHom U F).rangeRestrict ⁻¹' C) +
          ((countableUltralimitHom U F).rangeRestrict ⁻¹' D)) =
      loebMeasure U hU ((countableUltralimitHom U F).rangeRestrict ⁻¹' C) +
        loebMeasure U hU ((countableUltralimitHom U F).rangeRestrict ⁻¹' D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      ((countableUltralimitHom U F).rangeRestrict ⁻¹' C)
      ((countableUltralimitHom U F).rangeRestrict ⁻¹' D))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU)
      ((countableUltralimitHom U F).rangeRestrict ⁻¹' C)
      ((countableUltralimitHom U F).rangeRestrict ⁻¹' D))
    (hnoAE : ∀ J : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (J : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (J : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ J, t +ᵥ (((countableUltralimitHom U F).rangeRestrict ⁻¹' C) +
        ((countableUltralimitHom U F).rangeRestrict ⁻¹' D)) =ᵐ[loebMeasure U hU]
          ((countableUltralimitHom U F).rangeRestrict ⁻¹' C) +
            ((countableUltralimitHom U F).rangeRestrict ⁻¹' D)) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      ((countableUltralimitHom U F).rangeRestrict ⁻¹' C)
      ((countableUltralimitHom U F).rangeRestrict ⁻¹' D)) ∨
      Nonempty (InternalBohrPairData U hU q
        ((countableUltralimitHom U F).rangeRestrict ⁻¹' C)
        ((countableUltralimitHom U F).rangeRestrict ⁻¹' D)) := by
  letI : MetricSpace (ℕ → Additive Circle) := PiCountable.metricSpace
  let K := (countableUltralimitHom U F).range
  let φ := (countableUltralimitHom U F).rangeRestrict
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have hφ : Measurable φ := (measurable_countableUltralimitHom U F).subtype_mk
  have hφsurj : Function.Surjective φ := (countableUltralimitHom U F).rangeRestrict_surjective
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : ν.IsAddHaarMeasure := countableUltralimitHom_haar U hU F
  have hKclosed : IsClosed (K : Set (ℕ → Additive Circle)) :=
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace K)).isClosed
  have : PolishSpace K := hKclosed.polishSpace
  have hSm := measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc)
  let H := AddAction.aestabilizer K ν (C + D)
  have : IsClosed (H : Set K) := isClosed_aestabilizer ν (C + D) hSm
  let L := K ⧸ H
  letI : MeasurableSpace L := borel L
  letI : BorelSpace L := ⟨rfl⟩
  have : PolishSpace L := essential_stabilizer_quotient_polish ν (C + D) hSm
  have : MeasurableAdd₂ L := ⟨continuous_add.measurable⟩
  have : MeasurableNeg L := ⟨continuous_neg.measurable⟩
  let ψ := QuotientAddGroup.mk' H
  have hψ : Continuous ψ := QuotientAddGroup.continuous_mk
  have hψsurj : Function.Surjective ψ := QuotientAddGroup.mk'_surjective H
  have hker (t : K) : t ∈ ψ.ker ↔ t +ᵥ (C + D) =ᵐ[ν] C + D := by
    change ψ t = 0 ↔ t ∈ H
    exact QuotientAddGroup.eq_zero_iff t
  have hcharacters (J : OpenAddSubgroup L) (hJ : Nontrivial J) :
      ∃ χ : J →+ AddCircle (1 : ℝ), Continuous χ ∧ χ ≠ 0 := by
    letI : Nontrivial J := hJ
    exact exists_nontrivial_character_on_quotient_subgroup U hU F (C + D) hSm H
      (fun _ => Iff.rfl) J.toAddSubgroup
  rcases loeb_quotient_quasiPeriodic_or_literal_closedArc_cosets U hU q φ hφ hφsurj ψ hψ hψsurj
    C D hCsc hDsc hCpos hDpos hcomp hfull hirr hne hnoAE hker hcharacters with hQP | hmodel
  · exact Or.inl hQP
  obtain ⟨J, hconnected, u, v, e, he, hesymm, x, y, a, b, ha, hb, hab,
    hAsub, hBsub, hAmodel, hBmodel⟩ := hmodel
  exact Or.inr (exists_internalBohrPairData_of_compact_cosets U hU q F ψ hψ hψsurj
    (φ ⁻¹' C) (φ ⁻¹' D) J e he u v x y a b ha hb hab hAsub hBsub hAmodel hBmodel)

end Erdos335.Loeb

end
