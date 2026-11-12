import Erdos335.SubgroupAEMeasure
import Erdos335.CircleCharacterMeasure

/-!
# Transferring circle containers into a measured subgroup
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

theorem subgroup_circle_container_transfer
    {K : Type*} [AddCommGroup K] [MeasurableSpace K]
    (H : AddSubgroup K) [MeasurableSpace H]
    (μ : Measure K) (ν : Measure H) (c : ℝ≥0∞) (hc : c ≠ 0)
    (hmeasure : ∀ T : Set H, μ ((Subtype.val : H → K) '' T) = c * ν T)
    (S : Set K) (hSH : S ⊆ H)
    (e : H ≃+ AddCircle (1 : ℝ)) (he : Measurable e)
    (hmap : Measure.map e ν = volume) (T : Set (AddCircle (1 : ℝ)))
    (hsub : e.symm ⁻¹' ((Subtype.val : H → K) ⁻¹' S) ⊆ T)
    (hae : e.symm ⁻¹' ((Subtype.val : H → K) ⁻¹' S) =ᵐ[volume] T) :
    S ⊆ (Subtype.val : H → K) '' (e ⁻¹' T) ∧
      S =ᵐ[μ] (Subtype.val : H → K) '' (e ⁻¹' T) := by
  let C := (Subtype.val : H → K) ⁻¹' S
  have hEC : e ⁻¹' (e.symm ⁻¹' C) = C := by ext x; simp
  constructor
  · intro x hx
    let y : H := ⟨x, hSH hx⟩
    refine ⟨y, ?_, rfl⟩
    exact hsub (by change (e.symm (e y) : K) ∈ S; simpa using hx)
  · have haemap : e.symm ⁻¹' C =ᵐ[Measure.map e ν] T := by rwa [hmap]
    have hpre := ae_of_ae_map he.aemeasurable haemap
    change e ⁻¹' (e.symm ⁻¹' C) =ᵐ[ν] e ⁻¹' T at hpre
    rw [hEC] at hpre
    apply (ae_eq_subgroup_iff H μ ν c hc hmeasure S _ hSH (by
      rintro x ⟨y, _, rfl⟩
      exact y.property)).mpr
    simpa only [Subtype.coe_injective.preimage_image] using hpre

end Erdos335.Loeb
