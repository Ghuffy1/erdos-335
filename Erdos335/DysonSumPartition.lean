import Erdos335.DysonCosetDecomposition

/-!
# The remaining sum in the mixed-coset case

If the two exclusive parts contribute only to the periodic transformed
sum, every remaining sum comes from the two mixed parts.
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem dyson_sum_eq_periodic_union_mixed
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (A B : Set G)
    (hperiod : ((A ∪ B) + (A ∩ B)) + (H : Set G) = (A ∪ B) + (A ∩ B))
    (hleft : (A \ (B + (H : Set G))) + B ⊆ (A ∪ B) + (A ∩ B))
    (hright : A + (B \ (A + (H : Set G))) ⊆ (A ∪ B) + (A ∩ B)) :
    A + B = ((A ∪ B) + (A ∩ B)) ∪ (dysonMixedPart H A B + dysonMixedPart H B A) := by
  have hcommon (x : G) (hx : x ∈ (A ∩ B) + (H : Set G)) (y : G) (hy : y ∈ A ∪ B) :
      x + y ∈ (A ∪ B) + (A ∩ B) := by
    obtain ⟨i, hi, h, hh, hhx⟩ := hx
    have hmem : (y + i) + h ∈ ((A ∪ B) + (A ∩ B)) + (H : Set G) :=
      ⟨y + i, ⟨y, hy, i, hi, rfl⟩, h, hh, rfl⟩
    rw [hperiod] at hmem
    have heq : (y + i) + h = x + y := by
      change i + h = x at hhx
      rw [← hhx]
      abel
    rw [heq] at hmem
    exact hmem
  apply subset_antisymm
  · rintro z ⟨a, ha, b, hb, rfl⟩
    have ha' := ha
    rw [dyson_coset_partition H A B] at ha'
    rcases ha' with (haMixed | haCommon) | haOnly
    · have hb' := hb
      rw [dyson_coset_partition H B A] at hb'
      rcases hb' with (hbMixed | hbCommon) | hbOnly
      · exact Or.inr ⟨a, haMixed, b, hbMixed, rfl⟩
      · left
        have hbI : b ∈ (A ∩ B) + (H : Set G) := by simpa only [inter_comm B A] using hbCommon.2
        simpa only [add_comm b a] using hcommon b hbI a (Or.inl ha)
      · exact Or.inl (hright ⟨a, ha, b, hbOnly, rfl⟩)
    · exact Or.inl (hcommon a haCommon.2 b (Or.inr hb))
    · exact Or.inl (hleft ⟨a, haOnly, b, hb, rfl⟩)
  · rintro z (hz | hz)
    · obtain ⟨u, (hu | hu), v, hv, rfl⟩ := hz
      · exact ⟨u, hu, v, hv.2, rfl⟩
      · exact ⟨v, hv.1, u, hu, add_comm _ _⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := hz
      exact ⟨a, ha.1.1, b, hb.1.1, rfl⟩

end Erdos335.Loeb
