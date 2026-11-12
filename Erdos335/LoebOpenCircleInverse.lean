import Erdos335.OpenSubgroupFactorSets
import Erdos335.CompactOpenSubgroupFactor
import Erdos335.CircleSubgroupAperiodicity
import Erdos335.CircleSubgroupContainers
import Erdos335.LoebEmbeddingPairs
import Erdos335.LoebEmbeddingPeriods
import Erdos335.LoebAperiodicComplement
import Erdos335.LoebCircleInverse

/-!
# The inverse theorem inside an open circle subgroup
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance openCircleInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_open_circle_inverse
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
    [MeasurableAdd₂ K] [MeasurableNeg K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set K) (hCm : MeasurableSet C) (hDm : MeasurableSet D)
    (hSm : MeasurableSet (C + D))
    (hCpos : 0 < Measure.map φ (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map φ (loebMeasure U hU) D)
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
    (hperiod : ∀ t : K, t +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D → t = 0)
    (H : OpenAddSubgroup K) (hCH : C ⊆ H) (hDH : D ⊆ H)
    (e : H ≃+ AddCircle (1 : ℝ)) (he : Continuous e) (hesymm : Continuous e.symm) :
    ∃ x y : AddCircle (1 : ℝ), ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b < 1 ∧
      C ⊆ (Subtype.val : H → K) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 a))) ∧
      D ⊆ (Subtype.val : H → K) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b))) ∧
      C =ᵐ[Measure.map φ (loebMeasure U hU)]
        (Subtype.val : H → K) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 a))) ∧
      D =ᵐ[Measure.map φ (loebMeasure U hU)]
        (Subtype.val : H → K) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b))) := by
  have : IsTopologicalAddGroup H := inferInstanceAs (IsTopologicalAddGroup H.toAddSubgroup)
  have : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  have : MeasurableAdd₂ H := ⟨by
    exact ((measurable_subtype_coe.comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk⟩
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : ν.IsAddHaarMeasure := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  obtain ⟨r, p, hp, hrange, hpositive, ψ, hψ, hψsurj, hcomm⟩ :=
    exists_loeb_open_subgroup_coordinates U hU q φ hφ hsurj H
  let j := productMapHom (U : Filter ℕ) p
  let μr := loebMeasure (X := fun n => ZMod (r n : ℕ)) U hU
  let η := Measure.map ψ μr
  let c := μ (Set.range j)
  have hc : c ≠ ∞ := ne_of_lt (calc
    c ≤ μ univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ
    _ < ∞ := by simp)
  have : IsProbabilityMeasure μr := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure η := ⟨by
    rw [Measure.map_apply hψ MeasurableSet.univ]
    simp⟩
  have : η.IsAddHaarMeasure := loebMeasure_map_hom_isAddHaarMeasure U hU ψ hψ hψsurj
  have hrestriction := normalized_open_subgroup_measure ν H η
  have hνHpos : 0 < ν (H : Set K) := H.isOpen.measure_pos ν ⟨0, H.zero_mem⟩
  have hemap : Measure.map e η = volume :=
    map_haar_unitAddCircle_eq_volume η e.toAddMonoidHom he e.surjective
  let κ := e.toAddMonoidHom.comp ψ
  have hκ : Measurable κ := he.measurable.comp hψ
  have hκsurj : Function.Surjective κ := e.surjective.comp hψsurj
  have hκmap : Measure.map κ μr = volume := by
    change Measure.map (e ∘ ψ) μr = volume
    rw [← Measure.map_map he.measurable hψ]
    exact hemap
  let C0 := (Subtype.val : H → K) ⁻¹' C
  let D0 := (Subtype.val : H → K) ⁻¹' D
  let C1 := e.symm ⁻¹' C0
  let D1 := e.symm ⁻¹' D0
  let A := κ ⁻¹' C1
  let B := κ ⁻¹' D1
  have hC1m : MeasurableSet C1 := (hCm.preimage measurable_subtype_coe).preimage hesymm.measurable
  have hD1m : MeasurableSet D1 := (hDm.preimage measurable_subtype_coe).preimage hesymm.measurable
  have hsum0 : C0 + D0 = (Subtype.val : H → K) ⁻¹' (C + D) :=
    (subgroup_preimage_add H.toAddSubgroup C D hCH hDH).symm
  have hsum1 : C1 + D1 = e.symm ⁻¹' ((Subtype.val : H → K) ⁻¹' (C + D)) := by
    rw [show C1 + D1 = e.symm ⁻¹' (C0 + D0) from
      (preimage_add_of_surjective_addHom e.symm.toAddMonoidHom e.symm.surjective C0 D0).symm,
      hsum0]
  have hS1m : MeasurableSet (C1 + D1) := by
    rw [hsum1]
    exact (hSm.preimage measurable_subtype_coe).preimage hesymm.measurable
  have hκC : A = ψ ⁻¹' C0 := by ext z; simp [A, C1, κ]
  have hκD : B = ψ ⁻¹' D0 := by ext z; simp [B, D1, κ]
  have hAimage : j '' A = φ ⁻¹' C := by
    rw [hκC]
    exact image_preimage_subgroup_factor H.toAddSubgroup j φ ψ hcomm hrange C hCH
  have hBimage : j '' B = φ ⁻¹' D := by
    rw [hκD]
    exact image_preimage_subgroup_factor H.toAddSubgroup j φ ψ hcomm hrange D hDH
  have hSumimage : j '' (A + B) = (φ ⁻¹' C) + (φ ⁻¹' D) := by
    rw [Set.image_add j, hAimage, hBimage]
  have hm (T : Set ((U : Filter ℕ).Product (fun n => ZMod (r n : ℕ)))) :
      μ (j '' T) = c * μr T :=
    loebMeasure_image_injection U hU (fun n => p n) hp hpositive T
  have hApos : 0 < μr A := by
    apply (ENNReal.mul_pos_iff.mp (show 0 < c * μr A from ?_)).2
    rw [← hm, hAimage, ← Measure.map_apply hφ hCm]
    exact hCpos
  have hBpos : 0 < μr B := by
    apply (ENNReal.mul_pos_iff.mp (show 0 < c * μr B from ?_)).2
    rw [← hm, hBimage, ← Measure.map_apply hφ hDm]
    exact hDpos
  have hC1pos : 0 < volume C1 := by
    rw [← hκmap, Measure.map_apply hκ hC1m]
    exact hApos
  have hD1pos : 0 < volume D1 := by
    rw [← hκmap, Measure.map_apply hκ hD1m]
    exact hBpos
  have hfullr : μr (A + B) = μr A + μr B := by
    have h := hfull
    rw [← hSumimage, ← hAimage, ← hBimage, hm, hm, hm, ← mul_add] at h
    exact (ENNReal.mul_right_inj hpositive.ne' hc).mp h
  have hirrr : MeasureIrreducible μr (internalInnerMeasure U hU) A B :=
    loeb_irreducible_of_internal_embedding U hU p hp hpositive A B (by
      have h := hirr
      rw [← hAimage, ← hBimage] at h
      exact h)
  have hner : MeasureNonextendible μr (internalInnerMeasure U hU) A B :=
    loeb_nonextendible_of_internal_embedding U hU p hp hpositive A B (by
      have h := hne
      rw [← hAimage, ← hBimage] at h
      exact h)
  have hnor : ∀ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (r n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (r n : ℕ)))) →
      0 < μr (L : Set ((U : Filter ℕ).Product (fun n => ZMod (r n : ℕ)))) →
      ¬ ∀ t ∈ L, t +ᵥ (A + B) =ᵐ[μr] A + B :=
    loeb_no_positive_periods_of_internal_embedding U hU p hp hpositive (A + B) (by
      have h := hnoAE
      rw [← hSumimage] at h
      exact h)
  have hcompr : 0 < μr (A + B)ᶜ :=
    loeb_complement_pos_of_no_positive_periods U hU r (A + B) hnor
  have hSH : C + D ⊆ H := by
    rintro z ⟨a, ha, b, hb, rfl⟩
    exact H.add_mem (hCH ha) (hDH hb)
  have hperiod1 : ∀ z : AddCircle (1 : ℝ),
      z +ᵥ (C1 + D1) =ᵐ[volume] C1 + D1 → z = 0 := by
    rw [hsum1]
    exact subgroup_circle_aperiodic H.toAddSubgroup ν η (ν (H : Set K))
      hνHpos.ne' hrestriction (C + D) hSH hperiod e he.measurable hemap
  obtain ⟨x, y, a, b, ha, hb, hab, hCsub, hDsub, hCae, hDae⟩ :=
    loeb_unitCircle_inverse U hU r κ hκ hκsurj C1 D1 hC1m hD1m hS1m hC1pos hD1pos
      hcompr hfullr hirrr hner hnor hperiod1
  obtain ⟨hCcontain, hCmodel⟩ := subgroup_circle_container_transfer H.toAddSubgroup ν η
    (ν (H : Set K)) hνHpos.ne' hrestriction C hCH e he.measurable hemap _ hCsub hCae
  obtain ⟨hDcontain, hDmodel⟩ := subgroup_circle_container_transfer H.toAddSubgroup ν η
    (ν (H : Set K)) hνHpos.ne' hrestriction D hDH e he.measurable hemap _ hDsub hDae
  exact ⟨x, y, a, b, ha, hb, hab, hCcontain, hDcontain, hCmodel, hDmodel⟩

end Erdos335.Loeb

end
