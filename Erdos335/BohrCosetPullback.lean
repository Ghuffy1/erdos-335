import Erdos335.OpenSubgroupCharacterSets
import Erdos335.StabilizerPullback

/-!
# Pulling back a circle arc in a subgroup coset
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem preimage_subgroup_character_coset
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (φ : G →+ K) (H : AddSubgroup K) (e : H →+ AddCircle (1 : ℝ))
    (χ : K →+ AddCircle (1 : ℝ)) (hext : χ.comp H.subtype = e)
    (a : G) (S : Set (AddCircle (1 : ℝ))) :
    φ ⁻¹' (φ a +ᵥ ((Subtype.val : H → K) '' (e ⁻¹' S))) =
      (a +ᵥ (H.comap φ : Set G)) ∩ (χ.comp φ) ⁻¹' (χ (φ a) +ᵥ S) := by
  rw [subgroup_character_coset_preimage H e χ hext, preimage_inter, preimage_vadd_addHom]
  rfl

end Erdos335.Loeb
