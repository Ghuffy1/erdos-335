import Erdos335.LoebCircleLiteralContainment
import Erdos335.LoebCircleInputArcs
import Erdos335.CircleArcModels

/-!
# Closed-arc inverse theorem for an aperiodic circle factor
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance circleInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_unitCircle_inverse
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ)))
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hS : MeasurableSet (C + D))
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
    ∃ x y : AddCircle (1 : ℝ), ∃ p r : ℝ, 0 < p ∧ 0 < r ∧ p + r < 1 ∧
      C ⊆ x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) ∧
      D ⊆ y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r) ∧
      C =ᵐ[volume] x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) ∧
      D =ᵐ[volume] y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨hCmodel, hDmodel⟩ := loeb_unitCircle_pair_ae_closedArcs U hU q φ hφ hsurj C D
    hC hD hS hCpos hDpos hcomp hfull hirr hne hnoAE hperiod
  obtain ⟨x, p, hp, hpone, hCae⟩ := unitCircle_normalized_closedArcModel C hCmodel
  obtain ⟨y, r, hr, hrone, hDae⟩ := unitCircle_normalized_closedArcModel D hDmodel
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
  have mass (T : Set (AddCircle (1 : ℝ))) (hT : MeasurableSet T) :
      μ (φ ⁻¹' T) = volume T := by
    rw [← Measure.map_apply hφ hT, hvolume]
  have hCreal : (volume C).toReal = p := by
    rw [measure_congr hCae, volume_unitCircle_normalized_closedArc x p hpone.le,
      ENNReal.toReal_ofReal hp.le]
  have hDreal : (volume D).toReal = r := by
    rw [measure_congr hDae, volume_unitCircle_normalized_closedArc y r hrone.le,
      ENNReal.toReal_ofReal hr.le]
  have hSm : MeasurableSet ((φ ⁻¹' C) + (φ ⁻¹' D)) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D]
    exact hS.preimage hφ
  have hsumReal : (μ ((φ ⁻¹' C) + (φ ⁻¹' D))).toReal = p + r := by
    rw [hfull, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
      mass C hC, mass D hD, hCreal, hDreal]
  have htotal := congrArg ENNReal.toReal (measure_add_measure_compl (μ := μ) hSm)
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    hsumReal, measure_univ, ENNReal.toReal_one] at htotal
  have hpositiveComplement : 0 < (μ ((φ ⁻¹' C) + (φ ⁻¹' D))ᶜ).toReal :=
    ENNReal.toReal_pos hcomp.ne' (measure_ne_top μ _)
  have hsum : p + r < 1 := by linarith
  obtain ⟨hCsub, hDsub⟩ := loeb_unitCircle_literal_containment U hU q φ hφ hsurj C D
    hC hD hS hirr x y p r hp hr hsum hCae hDae
  exact ⟨x, y, p, r, hp, hr, hsum, hCsub, hDsub, hCae, hDae⟩

end Erdos335.Loeb

end
