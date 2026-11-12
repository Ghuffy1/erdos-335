import Erdos335.CircleArcMeasures
import Mathlib.MeasureTheory.Measure.Support

/-!
# Support of closed circle arcs and containment of translated supports
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Pointwise

namespace Erdos335.Loeb

theorem closure_unitCircle_openArc (a b : ℝ) (hab : a < b) :
    closure (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) =
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hclosed : IsClosed (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b) :=
    (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed
  apply subset_antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self) hclosed
  · rw [← closure_Ioo hab.ne]
    exact image_closure_subset_closure_image (AddCircle.continuous_mk' 1)

theorem support_unitCircle_closedArc (a b : ℝ) (hab : a < b) :
    (volume.restrict (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b)).support =
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let I : Set (AddCircle (1 : ℝ)) := ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b
  let J : Set (AddCircle (1 : ℝ)) := ((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b
  have hI : IsClosed I := (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed
  have hJ : IsOpen J := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hJI : J ⊆ I := image_mono Ioo_subset_Icc_self
  have hJsupport : J ⊆ (volume.restrict I).support := by
    intro x hx
    have hxi : x ∈ interior I := interior_mono hJI (by simpa only [hJ.interior_eq] using hx)
    have hxv : x ∈ (volume : Measure (AddCircle (1 : ℝ))).support := by
      rw [Measure.support_eq_univ]
      exact mem_univ x
    exact Measure.interior_inter_support ⟨hxi, hxv⟩
  apply subset_antisymm
  · intro x hx
    have h := Measure.support_restrict_subset (μ := (volume : Measure (AddCircle (1 : ℝ)))) (s := I) hx
    simpa only [hI.closure_eq] using h.1
  · have h := closure_minimal hJsupport (Measure.isClosed_support (μ := volume.restrict I))
    simpa only [I, J, closure_unitCircle_openArc a b hab] using h

theorem add_support_subset_of_sum_ae_subset
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (A B K : Set G) (hB : MeasurableSet B) (hK : IsClosed K)
    (hsum : A + B ≤ᵐ[μ] K) (a : G) (ha : a ∈ A) :
    a +ᵥ (μ.restrict B).support ⊆ K := by
  have hshift := (measurePreserving_add_left μ a).quasiMeasurePreserving.ae hsum
  have hpre : B ≤ᵐ[μ] (-a +ᵥ K) := by
    filter_upwards [hshift] with b hb hmem
    have h := hb ⟨a, ha, b, hmem, rfl⟩
    simpa only [vadd_set_eq_neg_preimage, mem_preimage, neg_neg] using h
  have hclosed : IsClosed (-a +ᵥ K) := by
    rw [vadd_set_eq_neg_preimage]
    exact hK.preimage (continuous_const.add continuous_id)
  have hmem : (-a +ᵥ K) ∈ ae (μ.restrict B) := by
    change ∀ᵐ b ∂μ.restrict B, b ∈ -a +ᵥ K
    rw [ae_restrict_iff' hB]
    exact hpre
  have hsupport := Measure.support_subset_of_isClosed hclosed hmem
  rintro x ⟨b, hb, rfl⟩
  have h := hsupport hb
  simpa only [vadd_set_eq_neg_preimage, mem_preimage, neg_neg, vadd_eq_add] using h

end Erdos335.Loeb
