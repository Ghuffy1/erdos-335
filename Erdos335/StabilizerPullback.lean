import Erdos335.LoebCompactEqualityReduction

/-!
# Stabilizers under surjective homomorphisms

Translations commute with pullback. A surjective homomorphism therefore
identifies the stabilizer of a pulled-back set with the pulled-back stabilizer.
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

variable {G K : Type*} [AddCommGroup G] [AddCommGroup K]

theorem preimage_vadd_addHom (φ : G →+ K) (S : Set K) (g : G) :
    φ ⁻¹' (φ g +ᵥ S) = g +ᵥ (φ ⁻¹' S) := by
  ext x
  constructor
  · rintro ⟨s, hs, hgs⟩
    refine ⟨x - g, ?_, by simp⟩
    change φ (x - g) ∈ S
    have heq : φ (x - g) = s := by
      rw [map_sub]
      change φ g + s = φ x at hgs
      rw [← hgs]
      abel
    rwa [heq]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨φ y, hy, ?_⟩
    change φ g + φ y = φ (g + y)
    exact (map_add φ g y).symm

theorem stabilizer_preimage_comap (φ : G →+ K) (hφ : Function.Surjective φ)
    (S : Set K) :
    AddAction.stabilizer G (φ ⁻¹' S) = (AddAction.stabilizer K S).comap φ := by
  ext g
  change g +ᵥ (φ ⁻¹' S) = φ ⁻¹' S ↔ φ g +ᵥ S = S
  rw [← preimage_vadd_addHom]
  constructor
  · intro heq
    ext y
    obtain ⟨x, rfl⟩ := hφ y
    exact Set.ext_iff.mp heq x
  · intro heq
    rw [heq]

theorem map_stabilizer_preimage (φ : G →+ K) (hφ : Function.Surjective φ)
    (S : Set K) :
    (AddAction.stabilizer G (φ ⁻¹' S)).map φ = AddAction.stabilizer K S := by
  rw [stabilizer_preimage_comap φ hφ S]
  exact AddSubgroup.map_comap_eq_self_of_surjective hφ _

end Erdos335.Loeb
