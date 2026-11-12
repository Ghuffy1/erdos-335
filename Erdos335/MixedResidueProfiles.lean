import Erdos335.NaturalCyclicProjection
import Mathlib.Tactic

/-!
# Divisibility and integer-mass obstructions for mixed terminal profiles
-/

set_option autoImplicit false

namespace Erdos335

theorem modulus_dvd_of_fiber_inclusion (N h k : ℕ+)
    (hhN : (h : ℕ) ∣ (N : ℕ)) (hkN : (k : ℕ) ∣ (N : ℕ))
    (s : ZMod (h : ℕ)) (t : ZMod (k : ℕ))
    (hsub : ∀ r : ZMod (N : ℕ), Loeb.naturalCyclicProjection N h r = s →
      Loeb.naturalCyclicProjection N k r = t) : (k : ℕ) ∣ (h : ℕ) := by
  obtain ⟨r, hr⟩ := Loeb.naturalCyclicProjection_surjective N h hhN s
  have hshift : Loeb.naturalCyclicProjection N h (r + (h : ℕ)) = s := by
    rw [map_add, Loeb.naturalCyclicProjection_natCast N h hhN]
    simp only [ZMod.natCast_self, add_zero, hr]
  have hkr := hsub r hr
  have hkshift := hsub (r + (h : ℕ)) hshift
  rw [map_add, Loeb.naturalCyclicProjection_natCast N k hkN, hkr] at hkshift
  have hz : ((h : ℕ) : ZMod (k : ℕ)) = 0 := by
    exact add_left_cancel (hkshift.trans (add_zero t).symm)
  exact (ZMod.natCast_eq_zero_iff (h : ℕ) (k : ℕ)).mp hz

theorem modulus_dvd_of_partial_profile (N h k : ℕ+)
    (hhN : (h : ℕ) ∣ (N : ℕ)) (hkN : (k : ℕ) ∣ (N : ℕ))
    (s : ZMod (h : ℕ)) (t : ZMod (k : ℕ)) (f : ZMod (N : ℕ) → ℝ)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hpartial : ∀ r, Loeb.naturalCyclicProjection N h r = s → f r = α)
    (hoff : ∀ r, Loeb.naturalCyclicProjection N k r ≠ t → f r = 0 ∨ f r = 1) :
    (k : ℕ) ∣ (h : ℕ) := by
  apply modulus_dvd_of_fiber_inclusion N h k hhN hkN s t
  intro r hr
  by_contra hn
  have hp := hpartial r hr
  rcases hoff r hn with hz | ho <;> linarith

theorem no_integer_and_partial_mass (h k : ℕ+) (hkh : (k : ℕ) ∣ (h : ℕ))
    (b β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (M L : ℤ)
    (hm : ((k : ℕ) : ℝ) * b = M)
    (hl : ((h : ℕ) : ℝ) * b = L + β) : False := by
  obtain ⟨d, hd⟩ := hkh
  have hcast : ((h : ℕ) : ℝ) = ((k : ℕ) : ℝ) * d := by exact_mod_cast hd
  have hmul : ((h : ℕ) : ℝ) * b = (d : ℝ) * M := by
    calc
      ((h : ℕ) : ℝ) * b = (d : ℝ) * (((k : ℕ) : ℝ) * b) := by rw [hcast]; ring
      _ = _ := by rw [hm]
  let z : ℤ := (d : ℤ) * M - L
  have hz : (z : ℝ) = β := by
    dsimp only [z]
    push_cast
    linarith
  have hz0 : (0 : ℤ) < z := by exact_mod_cast (show (0 : ℝ) < z by rw [hz]; exact hβ)
  have hz1 : z < (1 : ℤ) := by exact_mod_cast (show (z : ℝ) < 1 by rw [hz]; exact hβ1)
  omega

end Erdos335
