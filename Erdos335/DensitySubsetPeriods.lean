import Erdos335.PeriodicOutput
import Erdos335.MaskCoverage

/-!
# Equal-density subsets, exceptional fibers, and shift cancellation
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335

theorem densityEquivalent_of_subset_same_density
    (A B : Set ℕ) (d : ℝ) (hAB : A ⊆ B) (hA : HasDensity A d) (hB : HasDensity B d) :
    DensityEquivalent A B := by
  have hzero : Negligible (A \ B) := by
    rw [Set.sdiff_eq_empty.mpr hAB]
    exact hasDensity_empty
  refine ⟨hzero, ?_⟩
  change HasDensity (B \ A) 0
  simpa only [sub_self] using hB.sdiff_of_negligible_reverse hA hzero

theorem active_fiber_density_of_full_background
    (C : Set ℕ) (h : ℕ+) (u : ZMod (h : ℕ)) (c : ℝ)
    (hC : C ⊆ Set.Ioi 0) (hc : HasDensity C c)
    (hu : u ∈ residues (h : ℕ) C)
    (hbackground : ∀ r ∈ residues (h : ℕ) C, r ≠ u →
      Negligible (periodicSet ({r} : Finset (ZMod (h : ℕ))) \ C)) :
    HasDensity (residueFiber C u)
      (c - (((residues (h : ℕ) C).card : ℝ) - 1) / (h : ℕ)) := by
  classical
  let R := (residues (h : ℕ) C).erase u
  have hholes : Negligible (periodicSet R \ C) := by
    apply negligible_periodic_diff_of_singletons
    intro r hr
    exact hbackground r (Finset.mem_erase.mp hr).2 (Finset.mem_erase.mp hr).1
  have hd := hc.sdiff_of_negligible_reverse (hasDensity_periodicSet R) hholes
  have hset : C \ periodicSet R = residueFiber C u := by
    ext n
    constructor
    · rintro ⟨hn, hnR⟩
      have hnr : (n : ZMod (h : ℕ)) ∈ residues (h : ℕ) C := mem_residues.mpr ⟨n, hn, rfl⟩
      have hnu : (n : ZMod (h : ℕ)) = u := by
        by_contra hne
        exact hnR ⟨hC hn, Finset.mem_erase.mpr ⟨hne, hnr⟩⟩
      exact ⟨hn, hC hn, by simpa only [Finset.mem_singleton] using hnu⟩
    · rintro ⟨hn, hn0, hnu⟩
      refine ⟨hn, ?_⟩
      intro hnR
      exact (Finset.mem_erase.mp hnR.2).1 (by simpa only [Finset.mem_singleton] using hnu)
  have hcard : (R.card : ℝ) = ((residues (h : ℕ) C).card : ℝ) - 1 := by
    have hh : (R.card : ℝ) + 1 = (residues (h : ℕ) C).card := by
      exact_mod_cast Finset.card_erase_add_one hu
    linarith
  simpa only [hset, hcard] using hd

theorem shift_shift_eq (A : Set ℕ) (s t : ℕ) : shift (shift A s) t = shift A (s + t) := by
  ext n
  constructor
  · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (Nat.add_assoc a s t).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a + s, ⟨a, ha, rfl⟩, Nat.add_assoc a s t⟩

theorem DensityEquivalent.of_shift {A B : Set ℕ} (t : ℕ)
    (hAB : DensityEquivalent (Erdos335.shift A t) (Erdos335.shift B t)) : DensityEquivalent A B := by
  constructor
  · apply (negligible_shift_iff (A \ B) t).mp
    simpa only [shift_sdiff] using hAB.1
  · apply (negligible_shift_iff (B \ A) t).mp
    simpa only [shift_sdiff] using hAB.2

theorem period_of_equal_translates (A : Set ℕ) (x y : ℕ) (hxy : x ≤ y)
    (heq : DensityEquivalent (shift A x) (shift A y)) :
    DensityEquivalent (shift A (y - x)) A := by
  apply DensityEquivalent.of_shift x
  rw [shift_shift_eq, Nat.sub_add_cancel hxy]
  exact heq.symm

end Erdos335
