import Erdos335.NaturalQuotientRefinement

/-!
# Integer generators for the fibers of natural cyclic quotient maps
-/

set_option autoImplicit false

namespace Erdos335.Loeb

theorem naturalCyclicProjection_zero_iff_multiple (q t : ℕ+)
    (htq : (t : ℕ) ∣ (q : ℕ)) (x : ZMod (q : ℕ)) :
    naturalCyclicProjection q t x = 0 ↔ ∃ n : ℕ, ((n * (t : ℕ) : ℕ) : ZMod (q : ℕ)) = x := by
  constructor
  · intro hx
    rw [naturalCyclicProjection_val q t htq] at hx
    obtain ⟨n, hn⟩ := (ZMod.natCast_eq_zero_iff x.val (t : ℕ)).mp hx
    refine ⟨n, ?_⟩
    rw [Nat.mul_comm n, ← hn, ZMod.natCast_zmod_val]
  · rintro ⟨n, rfl⟩
    rw [naturalCyclicProjection_natCast q t htq, Nat.cast_mul, ZMod.natCast_self, mul_zero]

theorem naturalCyclicProjection_eq_iff_add_multiple (q t : ℕ+)
    (htq : (t : ℕ) ∣ (q : ℕ)) (x y : ZMod (q : ℕ)) :
    naturalCyclicProjection q t x = naturalCyclicProjection q t y ↔
      ∃ n : ℕ, x + ((n * (t : ℕ) : ℕ) : ZMod (q : ℕ)) = y := by
  constructor
  · intro hxy
    have hzero : naturalCyclicProjection q t (y - x) = 0 := by rw [map_sub, ← hxy, sub_self]
    obtain ⟨n, hn⟩ := (naturalCyclicProjection_zero_iff_multiple q t htq (y - x)).mp hzero
    exact ⟨n, by rw [hn]; abel⟩
  · rintro ⟨n, rfl⟩
    rw [map_add, (naturalCyclicProjection_zero_iff_multiple q t htq _).mpr ⟨n, rfl⟩, add_zero]

end Erdos335.Loeb
