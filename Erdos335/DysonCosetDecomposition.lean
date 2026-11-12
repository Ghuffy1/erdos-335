import Erdos335.QuasiPeriodicSets

/-!
# Coset parts in the Dyson transform argument

The mixed parts of A and B occupy the same cosets outside the saturation
of their intersection. These are the A₀ and B₀ parts in Griesmer's Lemma 5.20.
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G]

def dysonMixedPart (H : AddSubgroup G) (A B : Set G) : Set G :=
  (A ∩ (B + (H : Set G))) \ ((A ∩ B) + (H : Set G))

theorem dysonMixedPart_saturation_subset (H : AddSubgroup G) (A B : Set G) :
    dysonMixedPart H A B + (H : Set G) ⊆ dysonMixedPart H B A + (H : Set G) := by
  rintro x ⟨a, ⟨⟨ha, b, hb, k, hk, hka⟩, hout⟩, h, hh, rfl⟩
  change b + k = a at hka
  refine ⟨b, ⟨⟨hb, ?_⟩, ?_⟩, k + h, H.add_mem hk hh, ?_⟩
  · exact ⟨a, ha, -k, H.neg_mem hk, by rw [← hka]; abel⟩
  · rintro ⟨d, hd, l, hl, hlb⟩
    apply hout
    refine ⟨d, ⟨hd.2, hd.1⟩, l + k, H.add_mem hl hk, ?_⟩
    change d + l = b at hlb
    rw [← hka, ← hlb]
    abel
  · rw [← hka]
    abel

theorem dysonMixedPart_saturation_eq (H : AddSubgroup G) (A B : Set G) :
    dysonMixedPart H A B + (H : Set G) = dysonMixedPart H B A + (H : Set G) :=
  subset_antisymm (dysonMixedPart_saturation_subset H A B) (dysonMixedPart_saturation_subset H B A)

theorem dysonMixedPart_disjoint (H : AddSubgroup G) (A B : Set G) :
    Disjoint (dysonMixedPart H A B) B := by
  apply Set.disjoint_left.mpr
  intro x hx hxB
  exact hx.2 ⟨x, ⟨hx.1.1, hxB⟩, 0, H.zero_mem, add_zero x⟩

theorem dyson_coset_partition (H : AddSubgroup G) (A B : Set G) :
    A = (dysonMixedPart H A B ∪ (A ∩ ((A ∩ B) + (H : Set G)))) ∪
      (A \ (B + (H : Set G))) := by
  apply subset_antisymm
  · intro x hx
    by_cases hB : x ∈ B + (H : Set G)
    · by_cases hD : x ∈ (A ∩ B) + (H : Set G)
      · exact Or.inl (Or.inr ⟨hx, hD⟩)
      · exact Or.inl (Or.inl ⟨⟨hx, hB⟩, hD⟩)
    · exact Or.inr ⟨hx, hB⟩
  · rintro x ((hx | hx) | hx)
    · exact hx.1.1
    · exact hx.1
    · exact hx.1

end Erdos335.Loeb
