import Erdos335.CompactOpenSubgroupHaar
import Erdos335.StabilizerPullback

/-!
# Almost-everywhere equality inside a measured subgroup
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise symmDiff ENNReal

namespace Erdos335.Loeb

theorem subgroup_measure_preimage
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (H : AddSubgroup G) [MeasurableSpace H]
    (μ : Measure G) (ν : Measure H) (c : ℝ≥0∞)
    (hmeasure : ∀ T : Set H, μ ((Subtype.val : H → G) '' T) = c * ν T)
    (S : Set G) (hS : S ⊆ H) :
    μ S = c * ν ((Subtype.val : H → G) ⁻¹' S) := by
  have himage : (Subtype.val : H → G) '' ((Subtype.val : H → G) ⁻¹' S) = S := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    exact inter_eq_left.mpr hS
  rw [← hmeasure, himage]

theorem subgroup_preimage_add
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (A B : Set G) (hA : A ⊆ H) (hB : B ⊆ H) :
    (Subtype.val : H → G) ⁻¹' (A + B) =
      ((Subtype.val : H → G) ⁻¹' A) + ((Subtype.val : H → G) ⁻¹' B) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨⟨a, hA ha⟩, ha, ⟨b, hB hb⟩, hb, Subtype.ext hab⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem ae_eq_subgroup_iff
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (H : AddSubgroup G) [MeasurableSpace H]
    (μ : Measure G) (ν : Measure H) (c : ℝ≥0∞) (hc : c ≠ 0)
    (hmeasure : ∀ T : Set H, μ ((Subtype.val : H → G) '' T) = c * ν T)
    (A B : Set G) (hA : A ⊆ H) (hB : B ⊆ H) :
    A =ᵐ[μ] B ↔ (Subtype.val : H → G) ⁻¹' A =ᵐ[ν] (Subtype.val : H → G) ⁻¹' B := by
  have himage : (Subtype.val : H → G) ''
      (((Subtype.val : H → G) ⁻¹' A) ∆ ((Subtype.val : H → G) ⁻¹' B)) = A ∆ B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hxH : x ∈ H := by
        rcases symmDiff_subset_union hx with hxA | hxB
        · exact hA hxA
        · exact hB hxB
      exact ⟨⟨x, hxH⟩, hx, rfl⟩
  rw [← measure_symmDiff_eq_zero_iff, ← measure_symmDiff_eq_zero_iff,
    ← himage, hmeasure]
  simp only [mul_eq_zero, hc, false_or]

theorem ae_period_subgroup_iff
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (H : AddSubgroup G) [MeasurableSpace H]
    (μ : Measure G) (ν : Measure H) (c : ℝ≥0∞) (hc : c ≠ 0)
    (hmeasure : ∀ T : Set H, μ ((Subtype.val : H → G) '' T) = c * ν T)
    (S : Set G) (hS : S ⊆ H) (t : H) :
    (t : G) +ᵥ S =ᵐ[μ] S ↔
      t +ᵥ ((Subtype.val : H → G) ⁻¹' S) =ᵐ[ν] (Subtype.val : H → G) ⁻¹' S := by
  have htranslate : (t : G) +ᵥ S ⊆ (H : Set G) := by
    rintro x ⟨s, hs, rfl⟩
    exact H.add_mem t.property (hS hs)
  rw [ae_eq_subgroup_iff H μ ν c hc hmeasure _ S htranslate hS]
  change H.subtype ⁻¹' (H.subtype t +ᵥ S) =ᵐ[ν] H.subtype ⁻¹' S ↔ _
  rw [preimage_vadd_addHom H.subtype S t]
  rfl

end Erdos335.Loeb
