import Erdos335.CompactDysonTransform
import Mathlib.MeasureTheory.Group.AEStabilizer

/-!
# Translating compact pairs and their essential periods
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem translate_pair_sum
    {G : Type*} [AddCommGroup G] (A B : Set G) (a b : G) :
    (a +ᵥ A) + (b +ᵥ B) = (a + b) +ᵥ (A + B) := by
  ext z
  constructor
  · rintro ⟨x, ⟨u, hu, hux⟩, y, ⟨v, hv, hvy⟩, rfl⟩
    exact ⟨u + v, ⟨u, hu, v, hv, rfl⟩, by
      change a + u = x at hux
      change b + v = y at hvy
      change a + b + (u + v) = x + y
      rw [← hux, ← hvy]
      abel⟩
  · rintro ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    exact ⟨a + u, ⟨u, hu, rfl⟩, b + v, ⟨v, hv, rfl⟩, by
      change (a + u) + (b + v) = (a + b) + (u + v)
      abel⟩

theorem translate_set_difference
    {G : Type*} [AddCommGroup G] (B : Set G) (b : G) :
    (b +ᵥ B) - (b +ᵥ B) = B - B := by
  ext z
  constructor
  · rintro ⟨x, ⟨u, hu, hux⟩, y, ⟨v, hv, hvy⟩, rfl⟩
    exact ⟨u, hu, v, hv, by
      change b + u = x at hux
      change b + v = y at hvy
      rw [← hux, ← hvy]
      abel⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨b + u, ⟨u, hu, rfl⟩, b + v, ⟨v, hv, rfl⟩, by abel⟩

theorem ae_period_translate_iff
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] (S : Set G) (c t : G) :
    t +ᵥ (c +ᵥ S) =ᵐ[μ] c +ᵥ S ↔ t +ᵥ S =ᵐ[μ] S := by
  have hcomm : t +ᵥ (c +ᵥ S) = c +ᵥ (t +ᵥ S) := by
    rw [vadd_vadd, vadd_vadd, add_comm t c]
  rw [hcomm, vadd_set_ae_eq c]

end Erdos335.Loeb
