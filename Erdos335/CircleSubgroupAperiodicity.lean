import Erdos335.SubgroupAEMeasure
import Erdos335.CircleCharacterMeasure
import Erdos335.CompactDysonTransform

/-!
# Essential periods in circle coordinates of a subgroup
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace Erdos335.Loeb

theorem subgroup_circle_aperiodic
    {K : Type*} [AddCommGroup K] [MeasurableSpace K]
    (H : AddSubgroup K) [MeasurableSpace H]
    (μ : Measure K) (ν : Measure H) (c : ℝ≥0∞) (hc : c ≠ 0)
    (hmeasure : ∀ T : Set H, μ ((Subtype.val : H → K) '' T) = c * ν T)
    (S : Set K) (hSH : S ⊆ H)
    (hperiod : ∀ t : K, t +ᵥ S =ᵐ[μ] S → t = 0)
    (e : H ≃+ AddCircle (1 : ℝ)) (he : Measurable e)
    (hmap : Measure.map e ν = volume) :
    ∀ z : AddCircle (1 : ℝ),
      z +ᵥ (e.symm ⁻¹' ((Subtype.val : H → K) ⁻¹' S)) =ᵐ[volume]
        e.symm ⁻¹' ((Subtype.val : H → K) ⁻¹' S) → z = 0 := by
  intro z hz
  let T := (Subtype.val : H → K) ⁻¹' S
  let R := e.symm ⁻¹' T
  have hzmap : z +ᵥ R =ᵐ[Measure.map e ν] R := by rwa [hmap]
  have hpre := ae_of_ae_map he.aemeasurable hzmap
  change e ⁻¹' (z +ᵥ R) =ᵐ[ν] e ⁻¹' R at hpre
  have hER : e ⁻¹' R = T := by ext x; simp [R]
  have hshift : e ⁻¹' (z +ᵥ R) = e.symm z +ᵥ T := by
    rw [vadd_set_eq_neg_preimage, vadd_set_eq_neg_preimage]
    ext x
    simp only [mem_preimage, R, map_add, map_neg, e.symm_apply_apply]
  rw [hshift, hER] at hpre
  have hKperiod := (ae_period_subgroup_iff H μ ν c hc hmeasure S hSH (e.symm z)).mpr hpre
  have hzero : (e.symm z : K) = 0 := hperiod _ hKperiod
  have hsub : e.symm z = 0 := Subtype.ext hzero
  have hz0 := congrArg e hsub
  simpa using hz0

end Erdos335.Loeb
