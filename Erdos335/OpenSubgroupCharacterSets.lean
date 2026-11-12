import Erdos335.OpenSubgroupCharacterExtension
import Erdos335.LoebGroup

/-!
# A subgroup interval as a global-character pullback in one coset
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem subgroup_character_coset_preimage
    {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (e : H →+ AddCircle (1 : ℝ))
    (χ : G →+ AddCircle (1 : ℝ)) (hext : χ.comp H.subtype = e)
    (u : G) (S : Set (AddCircle (1 : ℝ))) :
    u +ᵥ ((Subtype.val : H → G) '' (e ⁻¹' S)) =
      (u +ᵥ (H : Set G)) ∩ χ ⁻¹' (χ u +ᵥ S) := by
  have hrestrict (h : H) : χ h = e h := DFunLike.congr_fun hext h
  ext z
  constructor
  · rintro ⟨w, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨⟨h, h.property, rfl⟩, ⟨e h, hh, ?_⟩⟩
    change χ u + e h = χ (u + h)
    rw [map_add, hrestrict]
  · rintro ⟨⟨h, hh, rfl⟩, ⟨t, ht, heq⟩⟩
    let h0 : H := ⟨h, hh⟩
    have hval : e h0 = t := by
      apply add_left_cancel (a := χ u)
      change χ u + e h0 = χ u + t
      rw [← hrestrict h0, ← map_add]
      exact heq.symm
    refine ⟨h, ⟨h0, ?_, rfl⟩, rfl⟩
    change e h0 ∈ S
    rwa [hval]

end Erdos335.Loeb
