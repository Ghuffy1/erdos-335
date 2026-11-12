import Erdos335.CompactQuotientRepresentative

/-!
# Saturated images under additive homomorphisms
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem preimage_image_subset_of_ker_invariant
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (φ : G →+ K) (P S : Set G) (hPS : P ⊆ S)
    (hperiod : ∀ h ∈ φ.ker, h +ᵥ S = S) :
    φ ⁻¹' (φ '' P) ⊆ S := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  have hker : x - p ∈ φ.ker := by
    change φ (x - p) = 0
    rw [map_sub, hpx, sub_self]
  have hmem : x ∈ (x - p) +ᵥ S := ⟨p, hPS hp, by simp [vadd_eq_add]⟩
  rwa [hperiod (x - p) hker] at hmem

theorem preimage_image_eq_of_ker_invariant
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (φ : G →+ K) (S : Set G)
    (hperiod : ∀ h ∈ φ.ker, h +ᵥ S = S) :
    φ ⁻¹' (φ '' S) = S :=
  subset_antisymm (preimage_image_subset_of_ker_invariant φ S S (Subset.refl S) hperiod)
    (subset_preimage_image φ S)

theorem preimage_image_add_eq_of_ker_invariant
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (φ : G →+ K) (P Q : Set G)
    (hperiod : ∀ h ∈ φ.ker, h +ᵥ (P + Q) = P + Q) :
    φ ⁻¹' ((φ '' P) + (φ '' Q)) = P + Q := by
  have himage : (φ '' P) + (φ '' Q) = φ '' (P + Q) := by
    ext z
    constructor
    · rintro ⟨a, ⟨p, hp, rfl⟩, b, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨p + q, add_mem_add hp hq, map_add φ p q⟩
    · rintro ⟨x, ⟨p, hp, q, hq, rfl⟩, rfl⟩
      exact ⟨φ p, mem_image_of_mem φ hp, φ q, mem_image_of_mem φ hq,
        (map_add φ p q).symm⟩
  rw [himage]
  exact preimage_image_eq_of_ker_invariant φ (P + Q) hperiod

end Erdos335.Loeb
