import Erdos335.LoebCircleArc
import Erdos335.LoebCompactInputAperiodicity
import Erdos335.LoebComplementStructure

/-!
# Complement duality recovers the first input's circle arc
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance circleComplementArcLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_unitCircle_complement_ae_arc
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
    ∃ c a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ b - a < 1 ∧
      (-(c : AddCircle (1 : ℝ)) +ᵥ Cᶜ) =ᵐ[volume]
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
  have mass (T : Set (AddCircle (1 : ℝ))) (hT : MeasurableSet T) :
      μ (φ ⁻¹' T) = volume T := by
    rw [← Measure.map_apply hφ hT, hvolume]
  let A := φ ⁻¹' C
  let B := φ ⁻¹' D
  let X := -B
  let Y := (A + B)ᶜ
  have hAm : MeasurableSet A := hC.preimage hφ
  have hBm : MeasurableSet B := hD.preimage hφ
  have hSm : MeasurableSet (A + B) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D]
    exact hS.preimage hφ
  have hApos : 0 < μ A := by rw [mass C hC]; exact hCpos
  have hBpos : 0 < μ B := by rw [mass D hD]; exact hDpos
  have hXm : MeasurableSet X := hBm.preimage (measurable_loeb_neg U hU)
  have hXpos : 0 < μ X := by
    change 0 < μ (-B)
    rwa [loebMeasure_neg U hU B hBm]
  obtain ⟨hEm, hEae, hEinner⟩ := loeb_nonextendible_complement_duality U hU q A B
    hAm hBm hSm hBpos hcomp hfull hne
  obtain ⟨hDualIrr, _, hDualNoAE⟩ := loeb_complement_dual_structure U hU q A B
    hAm hBm hSm hApos hBpos hcomp hfull hirr hne hnoAE
  have hDualFull : μ (X + Y) = μ X + μ Y :=
    (internalInnerMeasure_eq U hU _ hEm).symm.trans hEinner
  have hnegD : MeasurableSet (-D) := hD.preimage measurable_neg
  have hpreNeg : φ ⁻¹' (-D) = X := by
    ext x
    simp only [X, B, mem_preimage, Set.mem_neg, map_neg]
  have hpreComp : φ ⁻¹' (C + D)ᶜ = Y := by
    rw [preimage_compl, preimage_add_of_surjective_addHom φ hsurj C D]
  obtain ⟨P, hPsub, hPsc, hPm, hPmass⟩ := exists_full_measure_sigmaCompact_subset volume (-D) hnegD
  obtain ⟨Q, hQsub, hQsc, hQm, hQmass⟩ := exists_full_measure_sigmaCompact_subset volume (C + D)ᶜ hS.compl
  have hPQm : MeasurableSet (P + Q) :=
    measurableSet_of_sigmaCompact _ (isSigmaCompact_add_sets P Q hPsc hQsc)
  let R := φ ⁻¹' P
  let T := φ ⁻¹' Q
  have hRm : MeasurableSet R := hPm.preimage hφ
  have hTm : MeasurableSet T := hQm.preimage hφ
  have hRTm : MeasurableSet (R + T) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj P Q]
    exact hPQm.preimage hφ
  have hRX : R ⊆ X := by rw [← hpreNeg]; exact preimage_mono hPsub
  have hTY : T ⊆ Y := by rw [← hpreComp]; exact preimage_mono hQsub
  have hRmass : μ R = μ X := by
    rw [mass P hPm, hPmass, ← mass (-D) hnegD, hpreNeg]
  have hTmass : μ T = μ Y := by
    rw [mass Q hQm, hQmass, ← mass (C + D)ᶜ hS.compl, hpreComp]
  have hRae : R =ᵐ[μ] X := ae_eq_of_subset_of_measure_ge hRX hRmass.ge
    hRm.nullMeasurableSet (measure_ne_top μ _)
  have hTae : T =ᵐ[μ] Y := ae_eq_of_subset_of_measure_ge hTY hTmass.ge
    hTm.nullMeasurableSet (measure_ne_top μ _)
  have hRTmass : μ (R + T) = μ (X + Y) := by
    rw [← internalInnerMeasure_eq U hU _ hRTm, ← internalInnerMeasure_eq U hU _ hEm]
    exact hDualIrr R T hRm hTm hRX hTY hRmass hTmass
  have hRTae : R + T =ᵐ[μ] X + Y := ae_eq_of_subset_of_measure_ge
    (add_subset_add hRX hTY) hRTmass.ge hRTm.nullMeasurableSet (measure_ne_top μ _)
  obtain ⟨hRpos, hTpos, hRTfull, hRTirr, hRTne, hRTnoAE⟩ := loeb_ae_pair_model_structure U hU q
    X Y R T hXm hSm.compl hRm hTm hRTm hXpos hcomp hDualFull hDualIrr hDualNoAE hRae hTae hRTae
  have hRTA : R + T =ᵐ[μ] Aᶜ := hRTae.trans hEae
  have hcompactAE : P + Q =ᵐ[volume] Cᶜ := by
    have hpre := hRTA
    rw [← preimage_add_of_surjective_addHom φ hsurj P Q] at hpre
    have h := ae_map_set_eq_of_preimage μ φ hφ _ _ hPQm hC.compl hpre
    rwa [hvolume] at h
  have hRTcomp : 0 < μ (R + T)ᶜ := by
    have hc : (R + T)ᶜ =ᵐ[μ] A := by
      filter_upwards [hRTA] with x hx
      simpa only [mem_compl_iff, not_not] using congrArg Not hx
    rw [measure_congr hc]
    exact hApos
  have hCaper (t : AddCircle (1 : ℝ)) (ht : t +ᵥ C =ᵐ[volume] C) : t = 0 := by
    apply compact_factor_left_aperiodic_of_sum_aperiodic U hU q φ hφ hsurj C D hC hD hS hirr
    · intro z hz
      apply hperiod z
      rwa [hvolume] at hz
    · rwa [hvolume]
  have hPQaper (t : AddCircle (1 : ℝ)) (ht : t +ᵥ (P + Q) =ᵐ[volume] P + Q) : t = 0 := by
    have hcompl : t +ᵥ Cᶜ =ᵐ[volume] Cᶜ :=
      ((vadd_set_ae_eq t).2 hcompactAE).symm.trans (ht.trans hcompactAE)
    apply hCaper t
    rw [vadd_set_eq_neg_preimage] at hcompl ⊢
    rw [preimage_compl] at hcompl
    exact ae_eq_set_compl_compl.mp hcompl
  obtain ⟨c, a, b, ha, hab, hb, hlength, harc⟩ := loeb_unitCircle_sum_ae_arc U hU q φ hφ hsurj
    P Q hPm hQm hPQm (by rwa [mass P hPm] at hRpos) (by rwa [mass Q hQm] at hTpos)
    hRTcomp hRTfull hRTirr hRTne hRTnoAE hPQaper
  exact ⟨c, a, b, ha, hab, hb, hlength,
    ((vadd_set_ae_eq (-(c : AddCircle (1 : ℝ)))).2 hcompactAE).symm.trans harc⟩

end Erdos335.Loeb

end
