import Erdos335.CircleArcContainment
import Erdos335.IrreducibleSumContainer
import Erdos335.LoebCompactSumTransfer
import Erdos335.TranslatedCompactPairs
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Irreducible circle pairs lie literally in their closed-arc models
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance circleLiteralContainmentLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_unitCircle_literal_containment
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ)))
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hS : MeasurableSet (C + D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (x y : AddCircle (1 : ℝ)) (p r : ℝ) (hp : 0 < p) (hr : 0 < r) (hsum : p + r < 1)
    (hCmodel : C =ᵐ[volume] x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p))
    (hDmodel : D =ᵐ[volume] y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)) :
    C ⊆ x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) ∧
      D ⊆ y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r) := by
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
  let I := x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)
  let J := y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)
  let K := (x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + r))
  have hmeas (z : AddCircle (1 : ℝ)) (s : ℝ) :
      MeasurableSet (z +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s)) := by
    rw [vadd_set_eq_neg_preimage]
    exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed.measurableSet.preimage
      (measurable_const_add (-z))
  have hI : MeasurableSet I := hmeas x p
  have hJ : MeasurableSet J := hmeas y r
  have hK : MeasurableSet K := hmeas (x + y) (p + r)
  have hIJ : I + J = K := by
    dsimp [I, J, K]
    rw [translate_pair_sum, unitCircle_zero_closedArc_add p r hp.le hr.le]
  have hCpre : φ ⁻¹' C =ᵐ[μ] φ ⁻¹' I := by
    have h := hCmodel
    rw [← hvolume] at h
    exact ae_of_ae_map hφ.aemeasurable h
  have hDpre : φ ⁻¹' D =ᵐ[μ] φ ⁻¹' J := by
    have h := hDmodel
    rw [← hvolume] at h
    exact ae_of_ae_map hφ.aemeasurable h
  have hpreSum : MeasurableSet ((φ ⁻¹' C) + (φ ⁻¹' D)) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D]
    exact hS.preimage hφ
  have hpreContain : (φ ⁻¹' I) + (φ ⁻¹' J) ⊆ φ ⁻¹' K := by
    rw [← preimage_add_of_surjective_addHom φ hsurj I J, hIJ]
  have hpre := MeasureIrreducible.sum_ae_subset_of_ae_containers μ (internalInnerMeasure U hU)
    (fun _ _ h => internalInnerMeasure_mono U hU h)
    (fun T hTm => internalInnerMeasure_eq U hU T hTm)
    (φ ⁻¹' C) (φ ⁻¹' D) (φ ⁻¹' I) (φ ⁻¹' J) (φ ⁻¹' K)
    (hC.preimage hφ) (hD.preimage hφ) hpreSum (hI.preimage hφ) (hJ.preimage hφ)
    (hK.preimage hφ) hirr hCpre hDpre hpreContain
  rw [← preimage_add_of_surjective_addHom φ hsurj C D] at hpre
  have hpred : MeasurableSet {z : AddCircle (1 : ℝ) | z ∈ C + D → z ∈ K} := by
    convert hS.compl.union hK using 1
    ext z
    simp only [mem_setOf_eq, mem_union, mem_compl_iff]
    tauto
  have hmap : C + D ≤ᵐ[Measure.map φ μ] K := (ae_map_iff hφ.aemeasurable hpred).2 hpre
  have hcompact : C + D ≤ᵐ[volume] K := by rwa [hvolume] at hmap
  constructor
  · exact unitCircle_left_subset_of_ae_sum_container C D hD x y p r hp.le hr hsum hDmodel hcompact
  · have hswap : D + C ≤ᵐ[volume]
        (y + x) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (r + p)) := by
      simpa only [K, add_comm] using hcompact
    exact unitCircle_left_subset_of_ae_sum_container D C hC y x r p hr.le hp
      (by simpa only [add_comm] using hsum) hCmodel hswap

end Erdos335.Loeb

end
