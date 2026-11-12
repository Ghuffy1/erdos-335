import Erdos335.NaturalCyclicProjection
import Erdos335.DensityAlgebra

/-!
# Uniqueness of a single partial residue class under common refinement
-/

set_option autoImplicit false

open Set

namespace Erdos335

theorem partial_residue_profile_alignment
    (N h k : ℕ+) (hhN : (h : ℕ) ∣ (N : ℕ)) (hkN : (k : ℕ) ∣ (N : ℕ))
    (s : ZMod (h : ℕ)) (t : ZMod (k : ℕ))
    (S : Finset (ZMod (h : ℕ))) (T : Finset (ZMod (k : ℕ)))
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (f : ZMod (N : ℕ) → ℝ)
    (hh : ∀ r, f r = if Loeb.naturalCyclicProjection N h r = s then α
      else if Loeb.naturalCyclicProjection N h r ∈ S then 1 else 0)
    (hk : ∀ r, f r = if Loeb.naturalCyclicProjection N k r = t then β
      else if Loeb.naturalCyclicProjection N k r ∈ T then 1 else 0) :
    h = k ∧ α = β ∧
      ∀ r, Loeb.naturalCyclicProjection N h r = s ↔ Loeb.naturalCyclicProjection N k r = t := by
  classical
  have hpartial (r : ZMod (N : ℕ)) :
      Loeb.naturalCyclicProjection N h r = s ↔ Loeb.naturalCyclicProjection N k r = t := by
    constructor
    · intro hr
      have hleft := hh r
      rw [if_pos hr] at hleft
      by_contra hn
      have hright := hk r
      rw [if_neg hn] at hright
      split_ifs at hright <;> linarith
    · intro hr
      have hright := hk r
      rw [if_pos hr] at hright
      by_contra hn
      have hleft := hh r
      rw [if_neg hn] at hleft
      split_ifs at hleft <;> linarith
  have hsets : periodicSet ({s} : Finset (ZMod (h : ℕ))) =
      periodicSet ({t} : Finset (ZMod (k : ℕ))) := by
    ext n
    have hn := hpartial (n : ZMod (N : ℕ))
    rw [Loeb.naturalCyclicProjection_natCast N h hhN,
      Loeb.naturalCyclicProjection_natCast N k hkN] at hn
    simp only [periodicSet, Set.mem_setOf_eq, Finset.mem_singleton]
    exact and_congr_right (fun _ => hn)
  have hhd : HasDensity (periodicSet ({s} : Finset (ZMod (h : ℕ)))) ((1 : ℝ) / (h : ℕ)) := by
    simpa only [Finset.card_singleton, Nat.cast_one] using hasDensity_periodicSet ({s} : Finset (ZMod (h : ℕ)))
  have hkd : HasDensity (periodicSet ({t} : Finset (ZMod (k : ℕ)))) ((1 : ℝ) / (k : ℕ)) := by
    simpa only [Finset.card_singleton, Nat.cast_one] using hasDensity_periodicSet ({t} : Finset (ZMod (k : ℕ)))
  rw [← hsets] at hkd
  have hfrac := hhd.unique hkd
  have hreal : ((h : ℕ) : ℝ) = (k : ℕ) := by
    apply inv_injective
    simpa only [one_div] using hfrac
  have hnat : (h : ℕ) = (k : ℕ) := by exact_mod_cast hreal
  have hhk : h = k := Subtype.ext hnat
  obtain ⟨r, hr⟩ := Loeb.naturalCyclicProjection_surjective N h hhN s
  have hr' := (hpartial r).mp hr
  have hf1 := hh r
  have hf2 := hk r
  rw [if_pos hr] at hf1
  rw [if_pos hr'] at hf2
  exact ⟨hhk, hf1.symm.trans hf2, hpartial⟩

end Erdos335
