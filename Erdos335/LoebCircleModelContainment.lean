import Erdos335.LoebCompactSupport
import Erdos335.CircleArcContainment
import Erdos335.IrreducibleSumContainer
import Erdos335.TranslatedCompactPairs
import Erdos335.LoebInnerMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Literal containment for Loeb sets with circle-arc models
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance circleModelContainmentLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_unitCircle_left_subset_of_ae_sum_container
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hmap : Measure.map φ (loebMeasure U hU) = volume)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (x y : AddCircle (1 : ℝ)) (p r : ℝ) (hp : 0 ≤ p) (hr : 0 < r) (hsum : p + r < 1)
    (hB : B =ᵐ[loebMeasure U hU] φ ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)))
    (hcontainer : A + B ≤ᵐ[loebMeasure U hU]
      φ ⁻¹' ((x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + r)))) :
    A ⊆ φ ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)) := by
  let J := y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)
  let L := (x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + r))
  have closedArc (z : AddCircle (1 : ℝ)) (s : ℝ) :
      IsClosed (z +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s)) := by
    rw [vadd_set_eq_neg_preimage]
    exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed.preimage
      (continuous_const.add continuous_id)
  intro a ha
  have hsupport := loeb_add_support_subset_of_ae_sum_container U hU q φ hφ A B J L
    (closedArc y r).measurableSet (closedArc (x + y) (p + r)) hB hcontainer a ha
  rw [hmap, show J = y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r) from rfl,
    support_unitCircle_translated_closedArc y r hr] at hsupport
  exact unitCircle_translated_closedArc_erosion x y (φ a) p r hp hr.le hsum hsupport

theorem loeb_unitCircle_model_literal_containment
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hS : MeasurableSet (A + B))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (x y : AddCircle (1 : ℝ)) (p r : ℝ) (hp : 0 < p) (hr : 0 < r) (hsum : p + r < 1)
    (hAmodel : A =ᵐ[loebMeasure U hU] φ ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)))
    (hBmodel : B =ᵐ[loebMeasure U hU] φ ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r))) :
    A ⊆ φ ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)) ∧
      B ⊆ φ ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  have : IsProbabilityMeasure (Measure.map φ μ) := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : (Measure.map φ μ).IsAddHaarMeasure := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have hmap : Measure.map φ μ = volume := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  let I := x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)
  let J := y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)
  let L := (x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + r))
  have hclosed (z : AddCircle (1 : ℝ)) (s : ℝ) :
      IsClosed (z +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s)) := by
    rw [vadd_set_eq_neg_preimage]
    exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed.preimage
      (continuous_const.add continuous_id)
  have hIJ : (φ ⁻¹' I) + (φ ⁻¹' J) ⊆ φ ⁻¹' L := by
    rw [← preimage_add_of_surjective_addHom φ hsurj]
    have hsumIJ : I + J = L := by
      dsimp [I, J, L]
      rw [translate_pair_sum, unitCircle_zero_closedArc_add p r hp.le hr.le]
    rw [hsumIJ]
  have hcontainer := MeasureIrreducible.sum_ae_subset_of_ae_containers μ (internalInnerMeasure U hU)
    (fun _ _ h => internalInnerMeasure_mono U hU h)
    (fun T hT => internalInnerMeasure_eq U hU T hT)
    A B (φ ⁻¹' I) (φ ⁻¹' J) (φ ⁻¹' L) hA hB hS
    ((hclosed x p).measurableSet.preimage hφ) ((hclosed y r).measurableSet.preimage hφ)
    ((hclosed (x + y) (p + r)).measurableSet.preimage hφ) hirr hAmodel hBmodel hIJ
  constructor
  · exact loeb_unitCircle_left_subset_of_ae_sum_container U hU q φ hφ hmap A B x y p r hp.le hr
      hsum hBmodel hcontainer
  · have hswap : B + A ≤ᵐ[μ] φ ⁻¹'
        ((y + x) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (r + p))) := by
      simpa only [L, add_comm] using hcontainer
    exact loeb_unitCircle_left_subset_of_ae_sum_container U hU q φ hφ hmap B A y x r p hr.le hp
      (by simpa only [add_comm] using hsum) hAmodel hswap

end Erdos335.Loeb

end
