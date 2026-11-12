import Erdos335.CircleArcSupport
import Erdos335.CompactOpenSubgroupHaar

/-!
# Support of a closed arc in an open circle coset
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem support_image_Icc_of_isOpenMap
    {G : Type*} [TopologicalSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) (hμ : μ.support = univ)
    (f : ℝ → G) (hf : Continuous f) (hopen : IsOpenMap f) (a b : ℝ) (hab : a < b) :
    (μ.restrict (f '' Icc a b)).support = f '' Icc a b := by
  let I := f '' Icc a b
  let J := f '' Ioo a b
  have hI : IsClosed I := (isCompact_Icc.image hf).isClosed
  have hJ : IsOpen J := hopen _ isOpen_Ioo
  have hJI : J ⊆ I := image_mono Ioo_subset_Icc_self
  have hclosure : closure J = I := by
    apply subset_antisymm (closure_minimal hJI hI)
    dsimp [I, J]
    rw [← closure_Ioo hab.ne]
    exact image_closure_subset_closure_image hf
  have hsupport : J ⊆ (μ.restrict I).support := by
    intro x hx
    apply Measure.interior_inter_support
    constructor
    · exact interior_mono hJI (by simpa only [hJ.interior_eq] using hx)
    · rw [hμ]
      exact mem_univ x
  apply subset_antisymm
  · intro x hx
    have h := Measure.support_restrict_subset (μ := μ) (s := I) hx
    simpa only [hI.closure_eq] using h.1
  · have h := closure_minimal hsupport (Measure.isClosed_support (μ := μ.restrict I))
    rwa [hclosure] at h

theorem support_open_circle_arc
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure]
    (H : OpenAddSubgroup G) (e : H ≃+ AddCircle (1 : ℝ))
    (he : Continuous e) (hesymm : Continuous e.symm) (u : G)
    (x : AddCircle (1 : ℝ)) (p : ℝ) (hp : 0 < p) :
    (μ.restrict (u +ᵥ ((Subtype.val : H → G) ''
      (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)))))).support =
      u +ᵥ ((Subtype.val : H → G) ''
        (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)))) := by
  let E : H ≃ₜ AddCircle (1 : ℝ) := {
    toEquiv := e.toEquiv
    continuous_toFun := he
    continuous_invFun := hesymm
  }
  let f : ℝ → G := fun t => u + (e.symm (x + (t : AddCircle (1 : ℝ))) : G)
  have hf : Continuous f := continuous_const.add
    (continuous_subtype_val.comp (hesymm.comp (continuous_const.add (AddCircle.continuous_mk' 1))))
  have hopen : IsOpenMap f := (Homeomorph.addLeft u).isOpenMap.comp
    (H.isOpen.isOpenEmbedding_subtypeVal.isOpenMap.comp
      (E.symm.isOpenMap.comp ((Homeomorph.addLeft x).isOpenMap.comp
        QuotientAddGroup.isOpenMap_coe)))
  have himage : f '' Icc 0 p = u +ᵥ ((Subtype.val : H → G) ''
      (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)))) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨e.symm (x + (t : AddCircle (1 : ℝ))), ?_, rfl⟩
      exact ⟨e.symm (x + (t : AddCircle (1 : ℝ))), ⟨(t : AddCircle (1 : ℝ)), ⟨t, ht, rfl⟩, by simp⟩, rfl⟩
    · rintro ⟨w, ⟨h, ⟨s, ⟨t, ht, rfl⟩, heq⟩, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      dsimp [f]
      congr 2
      exact e.injective (by simpa using heq)
  rw [← himage]
  exact support_image_Icc_of_isOpenMap μ Measure.support_eq_univ f hf hopen 0 p hp

end Erdos335.Loeb
