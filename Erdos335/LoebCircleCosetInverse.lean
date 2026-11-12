import Erdos335.LoebOpenCircleInverse
import Erdos335.LoebPairCentering
import Erdos335.TranslatedCompactPairs

/-!
# Closed-arc containment in open circle cosets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance circleCosetInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_circle_coset_inverse
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
    (H : OpenAddSubgroup K) (u v : K)
    (hCH : C ⊆ u +ᵥ (H : Set K)) (hDH : D ⊆ v +ᵥ (H : Set K))
    (e : H ≃+ AddCircle (1 : ℝ)) (he : Continuous e) (hesymm : Continuous e.symm) :
    ∃ x y : AddCircle (1 : ℝ), ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b < 1 ∧
      C ⊆ u +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 a)))) ∧
      D ⊆ v +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b)))) ∧
      C =ᵐ[Measure.map φ (loebMeasure U hU)]
        u +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 a)))) ∧
      D =ᵐ[Measure.map φ (loebMeasure U hU)]
        v +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b)))) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : ν.IsAddHaarMeasure := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  let C0 := (-u) +ᵥ C
  let D0 := (-v) +ᵥ D
  have hC0m : MeasurableSet C0 := by
    rw [show C0 = (-u) +ᵥ C from rfl, vadd_set_eq_neg_preimage]
    exact hCm.preimage (measurable_const_add _)
  have hD0m : MeasurableSet D0 := by
    rw [show D0 = (-v) +ᵥ D from rfl, vadd_set_eq_neg_preimage]
    exact hDm.preimage (measurable_const_add _)
  have hsum0 : C0 + D0 = (-(u + v)) +ᵥ (C + D) := by
    rw [show C0 = (-u) +ᵥ C from rfl, show D0 = (-v) +ᵥ D from rfl,
      translate_pair_sum, neg_add]
  have hS0m : MeasurableSet (C0 + D0) := by
    rw [hsum0, vadd_set_eq_neg_preimage]
    exact hSm.preimage (measurable_const_add _)
  have hC0H : C0 ⊆ H := by
    rintro z ⟨c, hc, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hCH hc
    simpa only [vadd_eq_add, neg_add_cancel_left] using hh
  have hD0H : D0 ⊆ H := by
    rintro z ⟨d, hd, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hDH hd
    simpa only [vadd_eq_add, neg_add_cancel_left] using hh
  have mass (t : K) (S : Set K) : ν (t +ᵥ S) = ν S := by
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have hC0pos : 0 < ν C0 := by rw [mass]; exact hCpos
  have hD0pos : 0 < ν D0 := by rw [mass]; exact hDpos
  obtain ⟨α, hα⟩ := hsurj u
  obtain ⟨β, hβ⟩ := hsurj v
  have hpreC : φ ⁻¹' C0 = (-α) +ᵥ (φ ⁻¹' C) := by
    change φ ⁻¹' ((-u) +ᵥ C) = _
    rw [show -u = φ (-α) by rw [map_neg, hα], preimage_vadd_addHom]
  have hpreD : φ ⁻¹' D0 = (-β) +ᵥ (φ ⁻¹' D) := by
    change φ ⁻¹' ((-v) +ᵥ D) = _
    rw [show -v = φ (-β) by rw [map_neg, hβ], preimage_vadd_addHom]
  have loebmass (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) : μ (t +ᵥ S) = μ S :=
    loebMeasure_image_add_left U hU t S
  have hfull0 : μ ((φ ⁻¹' C0) + (φ ⁻¹' D0)) = μ (φ ⁻¹' C0) + μ (φ ⁻¹' D0) := by
    rw [hpreC, hpreD, translate_pair_sum, loebmass, loebmass, loebmass]
    exact hfull
  have hirr0 : MeasureIrreducible μ (internalInnerMeasure U hU) (φ ⁻¹' C0) (φ ⁻¹' D0) := by
    rw [hpreC, hpreD]
    exact loeb_irreducible_translate_pair U hU q _ _ hirr (-α) (-β)
  have hne0 : MeasureNonextendible μ (internalInnerMeasure U hU) (φ ⁻¹' C0) (φ ⁻¹' D0) := by
    rw [hpreC, hpreD]
    exact loeb_nonextendible_translate_pair U hU q _ _ hne (-α) (-β)
  have hno0 : ∀ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < μ (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ L, t +ᵥ ((φ ⁻¹' C0) + (φ ⁻¹' D0)) =ᵐ[μ] (φ ⁻¹' C0) + (φ ⁻¹' D0) := by
    intro L hLm hLpos ht
    apply hnoAE L hLm hLpos
    intro t htL
    have ht' := ht t htL
    rw [hpreC, hpreD, translate_pair_sum] at ht'
    exact (loeb_ae_period_translate_iff U hU q _ ((-α) + (-β)) t).mp ht'
  have hperiod0 : ∀ t : K, t +ᵥ (C0 + D0) =ᵐ[ν] C0 + D0 → t = 0 := by
    intro t ht
    rw [hsum0] at ht
    exact hperiod t ((ae_period_translate_iff ν (C + D) (-(u + v)) t).mp ht)
  obtain ⟨x, y, a, b, ha, hb, hab, hCsub, hDsub, hCae, hDae⟩ :=
    loeb_open_circle_inverse U hU q φ hφ hsurj C0 D0 hC0m hD0m hS0m hC0pos hD0pos
      hfull0 hirr0 hne0 hno0 hperiod0 H hC0H hD0H e he hesymm
  have hbackC : u +ᵥ C0 = C := by
    rw [show C0 = (-u) +ᵥ C from rfl, vadd_vadd, add_neg_cancel, zero_vadd]
  have hbackD : v +ᵥ D0 = D := by
    rw [show D0 = (-v) +ᵥ D from rfl, vadd_vadd, add_neg_cancel, zero_vadd]
  refine ⟨x, y, a, b, ha, hb, hab, ?_, ?_, ?_, ?_⟩
  · have h := image_mono (f := fun z : K => u + z) hCsub
    change u +ᵥ C0 ⊆ _ at h
    rwa [hbackC] at h
  · have h := image_mono (f := fun z : K => v + z) hDsub
    change v +ᵥ D0 ⊆ _ at h
    rwa [hbackD] at h
  · have h := (vadd_set_ae_eq u).mpr hCae
    rwa [hbackC] at h
  · have h := (vadd_set_ae_eq v).mpr hDae
    rwa [hbackD] at h

end Erdos335.Loeb

end
