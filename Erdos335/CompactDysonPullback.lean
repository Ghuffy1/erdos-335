import Erdos335.CompactDysonTransform

/-!
# Pulling Dyson transforms back along an additive homomorphism
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem preimage_dysonGroupLeft
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (φ : G →+ K) (C D : Set K) (e : G) :
    φ ⁻¹' dysonGroupLeft C D (φ e) =
      dysonGroupLeft (φ ⁻¹' C) (φ ⁻¹' D) e := by
  ext x
  simp only [dysonGroupLeft, mem_preimage, mem_union,
    vadd_set_eq_neg_preimage, map_add, map_neg]

theorem preimage_dysonGroupRight
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (φ : G →+ K) (C D : Set K) (e : G) :
    φ ⁻¹' dysonGroupRight C D (φ e) =
      dysonGroupRight (φ ⁻¹' C) (φ ⁻¹' D) e := by
  ext x
  simp only [dysonGroupRight, mem_preimage, mem_inter_iff, map_add]

end Erdos335.Loeb
