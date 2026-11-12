import Erdos335.LoebCompactSupport
import Erdos335.OpenCircleArcSupport
import Erdos335.EmbeddedCircleArcAlgebra
import Erdos335.IrreducibleSumContainer

/-!
# Literal recovery from open-circle coset models
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance openArcModelLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_open_circle_model_literal_containment
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
    [MeasurableAdd₂ K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hS : MeasurableSet (A + B))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (H : OpenAddSubgroup K) (e : H ≃+ AddCircle (1 : ℝ))
    (he : Continuous e) (hesymm : Continuous e.symm)
    (u v : K) (x y : AddCircle (1 : ℝ)) (p r : ℝ)
    (hp : 0 < p) (hr : 0 < r) (hsum : p + r < 1)
    (hAmodel : A =ᵐ[loebMeasure U hU] φ ⁻¹'
      (u +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p))))))
    (hBmodel : B =ᵐ[loebMeasure U hU] φ ⁻¹'
      (v +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)))))) :
    A ⊆ φ ⁻¹' (u +ᵥ ((Subtype.val : H → K) ''
      (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p))))) ∧
      B ⊆ φ ⁻¹' (v +ᵥ ((Subtype.val : H → K) ''
        (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r))))) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : ν.IsAddHaarMeasure := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  let f := H.toAddSubgroup.subtype.comp e.symm.toAddMonoidHom
  have hf : Continuous f := continuous_subtype_val.comp hesymm
  have hfinj : Function.Injective f := Subtype.coe_injective.comp e.symm.injective
  let I := u +ᵥ (f '' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)))
  let J := v +ᵥ (f '' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)))
  let L := (u + v) +ᵥ (f '' ((x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + r))))
  have hIeq : I = u +ᵥ ((Subtype.val : H → K) ''
      (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)))) := by
    exact congrArg (fun T : Set K => u +ᵥ T)
      (subgroup_circle_arc_image H.toAddSubgroup e _).symm
  have hJeq : J = v +ᵥ ((Subtype.val : H → K) ''
      (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)))) := by
    exact congrArg (fun T : Set K => v +ᵥ T)
      (subgroup_circle_arc_image H.toAddSubgroup e _).symm
  have hAm : A =ᵐ[μ] φ ⁻¹' I := by rw [hIeq]; exact hAmodel
  have hBm : B =ᵐ[μ] φ ⁻¹' J := by rw [hJeq]; exact hBmodel
  have hclosed (w : K) (z : AddCircle (1 : ℝ)) (s : ℝ) :
      IsClosed (w +ᵥ (f '' (z +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s)))) := by
    have hbase : IsCompact (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s) :=
      isCompact_Icc.image (AddCircle.continuous_mk' 1)
    have hshift : IsCompact (z +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s)) :=
      hbase.image (continuous_const.add continuous_id)
    exact ((hshift.image hf).image (continuous_const.add continuous_id)).isClosed
  have hIclosed : IsClosed I := hclosed u x p
  have hJclosed : IsClosed J := hclosed v y r
  have hLclosed : IsClosed L := hclosed (u + v) (x + y) (p + r)
  have hIJ : I + J = L := embedded_closedArc_add f u v x y p r hp.le hr.le
  have hpreIJ : (φ ⁻¹' I) + (φ ⁻¹' J) ⊆ φ ⁻¹' L := by
    rw [← preimage_add_of_surjective_addHom φ hsurj, hIJ]
  have hcontainer := MeasureIrreducible.sum_ae_subset_of_ae_containers μ (internalInnerMeasure U hU)
    (fun _ _ h => internalInnerMeasure_mono U hU h)
    (fun T hT => internalInnerMeasure_eq U hU T hT)
    A B (φ ⁻¹' I) (φ ⁻¹' J) (φ ⁻¹' L) hA hB hS
    (hIclosed.measurableSet.preimage hφ) (hJclosed.measurableSet.preimage hφ)
    (hLclosed.measurableSet.preimage hφ) hirr hAm hBm hpreIJ
  have hIsupport : (ν.restrict I).support = I := by
    rw [hIeq]
    exact support_open_circle_arc ν H e he hesymm u x p hp
  have hJsupport : (ν.restrict J).support = J := by
    rw [hJeq]
    exact support_open_circle_arc ν H e he hesymm v y r hr
  have hmain : A ⊆ φ ⁻¹' I ∧ B ⊆ φ ⁻¹' J := by
    constructor
    · intro a ha
      have h := loeb_add_support_subset_of_ae_sum_container U hU q φ hφ A B J L
        hJclosed.measurableSet hLclosed hBm hcontainer a ha
      change φ a +ᵥ (ν.restrict J).support ⊆ L at h
      rw [hJsupport] at h
      exact embedded_closedArc_erosion f hfinj u v (φ a) x y p r hp.le hr.le hsum h
    · intro b hb
      have hswap : B + A ≤ᵐ[μ] φ ⁻¹' L := by rw [add_comm B A]; exact hcontainer
      have h := loeb_add_support_subset_of_ae_sum_container U hU q φ hφ B A I L
        hIclosed.measurableSet hLclosed hAm hswap b hb
      change φ b +ᵥ (ν.restrict I).support ⊆ L at h
      rw [hIsupport] at h
      have h' : φ b +ᵥ (u +ᵥ (f '' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)))) ⊆
          (v + u) +ᵥ (f '' ((y + x) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (r + p)))) := by
        simpa only [I, L, add_comm] using h
      exact embedded_closedArc_erosion f hfinj v u (φ b) y x r p hr.le hp.le
        (by simpa only [add_comm] using hsum) h'
  simpa only [hIeq, hJeq] using hmain

end Erdos335.Loeb

end
