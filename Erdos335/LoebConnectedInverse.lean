import Erdos335.LoebCompactCircleModel
import Erdos335.LoebCircleInverse
import Erdos335.CircleCharacterMeasure
import Erdos335.StabilizerPullback

/-!
# Closed-arc alternatives in a connected compact factor
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance connectedInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_connected_compact_quasiPeriodic_or_closedArcs
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [ConnectedSpace K] [T2Space K] [PolishSpace K]
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
    (hperiod : ∀ z : K, z +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D → z = 0)
    (χ : K →+ AddCircle (1 : ℝ)) (hχ : Continuous χ) (hχne : χ ≠ 0) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨
    ∃ e : K ≃+ AddCircle (1 : ℝ), Continuous e ∧ Continuous e.symm ∧
      ∃ x y : AddCircle (1 : ℝ), ∃ p r : ℝ, 0 < p ∧ 0 < r ∧ p + r < 1 ∧
        C ⊆ e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)) ∧
        D ⊆ e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)) ∧
        C =ᵐ[Measure.map φ (loebMeasure U hU)] e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)) ∧
        D =ᵐ[Measure.map φ (loebMeasure U hU)] e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)) := by
  rcases loeb_compact_quasiPeriodic_or_circle_model U hU q φ hφ hsurj C D hCsc hDsc
    hCpos hDpos hcomp hfull hirr hne hnoAE hperiod χ hχ hχne with hQP | hcircle
  · exact Or.inl hQP
  right
  obtain ⟨e, he, hesymm⟩ := hcircle
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : ν.IsAddHaarMeasure := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have hmapE : Measure.map e ν = volume := map_haar_unitAddCircle_eq_volume ν e.toAddMonoidHom he e.surjective
  let ψ := e.toAddMonoidHom.comp φ
  have hψ : Measurable ψ := he.measurable.comp hφ
  have hψsurj : Function.Surjective ψ := e.surjective.comp hsurj
  have hmapψ : Measure.map ψ μ = volume := by
    have h := hmapE
    rw [Measure.map_map he.measurable hφ] at h
    exact h
  let C' := e.symm ⁻¹' C
  let D' := e.symm ⁻¹' D
  have hC := measurableSet_of_sigmaCompact C hCsc
  have hD := measurableSet_of_sigmaCompact D hDsc
  have hS := measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc)
  have hC' : MeasurableSet C' := hC.preimage hesymm.measurable
  have hD' : MeasurableSet D' := hD.preimage hesymm.measurable
  have hsum' : C' + D' = e.symm ⁻¹' (C + D) :=
    (preimage_add_of_surjective_addHom e.symm.toAddMonoidHom e.symm.surjective C D).symm
  have hS' : MeasurableSet (C' + D') := by rw [hsum']; exact hS.preimage hesymm.measurable
  have hEC : e ⁻¹' C' = C := by ext z; simp [C']
  have hED : e ⁻¹' D' = D := by ext z; simp [D']
  have hES : e ⁻¹' (C' + D') = C + D := by rw [hsum']; ext z; simp
  have hψC : ψ ⁻¹' C' = φ ⁻¹' C := by ext z; simp [ψ, C']
  have hψD : ψ ⁻¹' D' = φ ⁻¹' D := by ext z; simp [ψ, D']
  have hψS : (ψ ⁻¹' C') + (ψ ⁻¹' D') = (φ ⁻¹' C) + (φ ⁻¹' D) := by rw [hψC, hψD]
  have mass' (T : Set (AddCircle (1 : ℝ))) (hT : MeasurableSet T) : μ (ψ ⁻¹' T) = volume T := by
    rw [← Measure.map_apply hψ hT, hmapψ]
  have hCpos' : 0 < volume C' := by
    rw [← mass' C' hC', hψC, ← Measure.map_apply hφ hC]
    exact hCpos
  have hDpos' : 0 < volume D' := by
    rw [← mass' D' hD', hψD, ← Measure.map_apply hφ hD]
    exact hDpos
  have hperiod' (z : AddCircle (1 : ℝ)) (hz : z +ᵥ (C' + D') =ᵐ[volume] C' + D') : z = 0 := by
    have hmap : z +ᵥ (C' + D') =ᵐ[Measure.map e ν] C' + D' := by rwa [hmapE]
    have hp := ae_of_ae_map he.measurable.aemeasurable hmap
    change e ⁻¹' (z +ᵥ (C' + D')) =ᵐ[ν] e ⁻¹' (C' + D') at hp
    have hset : e ⁻¹' (z +ᵥ (C' + D')) = e.symm z +ᵥ (C + D) := by
      rw [hsum', vadd_set_eq_neg_preimage, vadd_set_eq_neg_preimage]
      ext w
      simp only [mem_preimage, map_add, map_neg, e.symm_apply_apply]
    rw [hset, hES] at hp
    have hezero := hperiod (e.symm z) hp
    have h := congrArg e hezero
    simpa using h
  obtain ⟨x, y, p, r, hp, hr, hpr, hCsub, hDsub, hCae, hDae⟩ :=
    loeb_unitCircle_inverse U hU q ψ hψ hψsurj C' D' hC' hD' hS' hCpos' hDpos'
      (by simpa only [hψS] using hcomp)
      (by simpa only [hψS, hψC, hψD] using hfull)
      (by simpa only [hψC, hψD] using hirr)
      (by simpa only [hψC, hψD] using hne)
      (by simpa only [hψS] using hnoAE) hperiod'
  refine ⟨e, he, hesymm, x, y, p, r, hp, hr, hpr, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hCsub (by change e.symm (e z) ∈ C; simpa using hz)
  · intro z hz
    exact hDsub (by change e.symm (e z) ∈ D; simpa using hz)
  · have hmap : C' =ᵐ[Measure.map e ν] x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) := by
      rwa [hmapE]
    have h := ae_of_ae_map he.measurable.aemeasurable hmap
    change e ⁻¹' C' =ᵐ[ν] e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)) at h
    rwa [hEC] at h
  · have hmap : D' =ᵐ[Measure.map e ν] y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r) := by
      rwa [hmapE]
    have h := ae_of_ae_map he.measurable.aemeasurable hmap
    change e ⁻¹' D' =ᵐ[ν] e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)) at h
    rwa [hED] at h

end Erdos335.Loeb

end
