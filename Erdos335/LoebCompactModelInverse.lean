import Erdos335.LoebCountableCompactInverse
import Erdos335.LoebAEModelStructure
import Erdos335.LoebOpenArcModelContainment

/-!
# The compact-model inverse theorem for the original Loeb inputs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance compactModelInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U
local instance compactModelInverseCircleSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance compactModelInverseCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem loeb_countable_model_quasiPeriodic_or_internalBohr
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (F : ℕ → ∀ n, ZMod (q n : ℕ) →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hcompAB : 0 < loebMeasure U hU (A + B)ᶜ)
    (hfullAB : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirrAB : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hneAB : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAB : ∀ J : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (J : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (J : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ J, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B)
    (C D : Set (countableUltralimitHom U F).range) (hCsc : IsSigmaCompact C) (hDsc : IsSigmaCompact D)
    (hCA : (countableUltralimitHom U F).rangeRestrict ⁻¹' C =ᵐ[loebMeasure U hU] A)
    (hDB : (countableUltralimitHom U F).rangeRestrict ⁻¹' D =ᵐ[loebMeasure U hU] B)
    (hSum : (countableUltralimitHom U F).rangeRestrict ⁻¹' (C + D) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) ∨
      Nonempty (InternalBohrPairData U hU q A B) := by
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
  let P := φ ⁻¹' C
  let Q := φ ⁻¹' D
  have hCm := measurableSet_of_sigmaCompact C hCsc
  have hDm := measurableSet_of_sigmaCompact D hDsc
  have hCDm := measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc)
  have hPm : MeasurableSet P := hCm.preimage hφ
  have hQm : MeasurableSet Q := hDm.preimage hφ
  have hPQm : MeasurableSet (P + Q) := by
    rw [show P + Q = φ ⁻¹' (C + D) from (preimage_add_of_surjective_addHom φ hφsurj C D).symm]
    exact hCDm.preimage hφ
  have hPQae : P + Q =ᵐ[μ] A + B := by
    rw [show P + Q = φ ⁻¹' (C + D) from (preimage_add_of_surjective_addHom φ hφsurj C D).symm]
    exact hSum
  obtain ⟨hPpos, hQpos, hfull, hirr, hne, hnoAE⟩ := loeb_ae_pair_model_structure U hU q
    A B P Q hAm hBm hPm hQm hPQm hApos hBpos hfullAB hirrAB hnoAB hCA hDB hPQae
  have hcomp : 0 < μ (P + Q)ᶜ := by
    have hcae : (P + Q)ᶜ =ᵐ[μ] (A + B)ᶜ := by
      filter_upwards [hPQae] with z hz
      exact congrArg Not hz
    rwa [measure_congr hcae]
  have hCpos : 0 < ν C := by rw [Measure.map_apply hφ hCm]; exact hPpos
  have hDpos : 0 < ν D := by rw [Measure.map_apply hφ hDm]; exact hQpos
  let H := AddAction.aestabilizer K ν (C + D)
  have : IsClosed (H : Set K) := isClosed_aestabilizer ν (C + D) hCDm
  let L := K ⧸ H
  letI : MeasurableSpace L := borel L
  letI : BorelSpace L := ⟨rfl⟩
  have : PolishSpace L := essential_stabilizer_quotient_polish ν (C + D) hCDm
  have : MeasurableAdd₂ L := ⟨continuous_add.measurable⟩
  have : MeasurableNeg L := ⟨continuous_neg.measurable⟩
  let ψ := QuotientAddGroup.mk' H
  have hψ : Continuous ψ := QuotientAddGroup.continuous_mk
  have hψsurj : Function.Surjective ψ := QuotientAddGroup.mk'_surjective H
  have hker (z : K) : z ∈ ψ.ker ↔ z +ᵥ (C + D) =ᵐ[ν] C + D := by
    change ψ z = 0 ↔ z ∈ H
    exact QuotientAddGroup.eq_zero_iff z
  have hcharacters (J : OpenAddSubgroup L) (hJ : Nontrivial J) :
      ∃ χ : J →+ AddCircle (1 : ℝ), Continuous χ ∧ χ ≠ 0 := by
    letI : Nontrivial J := hJ
    exact exists_nontrivial_character_on_quotient_subgroup U hU F (C + D) hCDm H
      (fun _ => Iff.rfl) J.toAddSubgroup
  rcases loeb_quotient_quasiPeriodic_or_literal_closedArc_cosets U hU q φ hφ hφsurj ψ hψ hψsurj
    C D hCsc hDsc hCpos hDpos hcomp hfull hirr hne hnoAE hker hcharacters with hQP | hmodel
  · obtain ⟨p⟩ := hQP
    exact Or.inl (loeb_quasiPeriodic_pair_of_equal_sum_model U hU q A B P Q p hPQm hPQae
      hAm hBm hSm hApos hBpos hcompAB hfullAB hirrAB hneAB hnoAB)
  obtain ⟨J, hconnected, u, v, e, he, hesymm, x, y, a, b, ha, hb, hab,
    hPsub, hQsub, hPmodel, hQmodel⟩ := hmodel
  let θ := ψ.comp φ
  have hθ : Measurable θ := hψ.measurable.comp hφ
  have hθsurj : Function.Surjective θ := hψsurj.comp hφsurj
  have hAmodel := hCA.symm.trans hPmodel
  have hBmodel := hDB.symm.trans hQmodel
  obtain ⟨hAsub, hBsub⟩ := loeb_open_circle_model_literal_containment U hU q θ hθ hθsurj A B
    hAm hBm hSm hirrAB J e he hesymm u v x y a b ha hb hab hAmodel hBmodel
  exact Or.inr (exists_internalBohrPairData_of_compact_cosets U hU q F ψ hψ hψsurj A B
    J e he u v x y a b ha hb hab hAsub hBsub hAmodel hBmodel)

end Erdos335.Loeb

end
