import Erdos335.OrdinaryPositiveFrame

/-!
# The active-section density equation inside an actual finite frame

Private proof development. Verification status is recorded separately.
Ordinary density of the total sumset supplies the active output density.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem FiniteFrame.active_sections_sum_hasDensity
    {A B : Set ℕ} (f : FiniteFrame A B)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (a b x y : ℝ) (hA : HasDensity A a) (hB : HasDensity B b)
    (hC : HasDensity (A + B) (a + b))
    (hactiveA : HasDensity (residueSection A f.modulus f.activeA) x)
    (hactiveB : HasDensity (residueSection B f.modulus f.activeB) y) :
    HasDensity (residueSection A f.modulus f.activeA + residueSection B f.modulus f.activeB)
      (x + y) := by
  classical
  let q := f.modulus
  let SA := residues (q : ℕ) A
  let SB := residues (q : ℕ) B
  let C := A + B
  let u := f.activeA + f.activeB
  let W := residues (q : ℕ) C
  let R := W.erase u
  have hCpos : C ⊆ Set.Ioi 0 := sumset_positive hApos hBpos
  have hu : u ∈ W := by
    dsimp only [W, C, u]
    rw [residues_add]
    exact Finset.add_mem_add f.activeA_mem f.activeB_mem
  have hholes : Negligible (periodicSet R \ C) := by
    apply negligible_periodic_diff_of_singletons
    intro r hr
    have hr' := Finset.mem_erase.mp hr
    exact f.output_background hApos hBpos hr'.2 hr'.1
  have hactiveSet : C \ periodicSet R = residueFiber C u := by
    ext n
    constructor
    · rintro ⟨hn, hnR⟩
      have hn0 : 0 < n := hCpos hn
      have hnr : (n : ZMod (q : ℕ)) ∈ W := mem_residues.mpr ⟨n, hn, rfl⟩
      have hnu : (n : ZMod (q : ℕ)) = u := by
        by_contra hne
        exact hnR ⟨hn0, Finset.mem_erase.mpr ⟨hne, hnr⟩⟩
      exact ⟨hn, hn0, by simpa only [Finset.mem_singleton] using hnu⟩
    · rintro ⟨hn, hn0, hnr⟩
      have hnu : (n : ZMod (q : ℕ)) = u := by simpa only [Finset.mem_singleton] using hnr
      refine ⟨hn, ?_⟩
      intro hnR
      exact (Finset.mem_erase.mp hnR.2).1 hnu
  have hactiveC := hC.sdiff_of_negligible_reverse (hasDensity_periodicSet R) hholes
  rw [hactiveSet] at hactiveC
  have hFA := hasDensity_residueFiber hApos hactiveA
  have hFB := hasDensity_residueFiber hBpos hactiveB
  have hfromA := hasDensity_from_residue_background A q f.activeA (x / q) hApos f.activeA_mem
    (fun r hr hne => missing_fiber_of_full_section hApos (f.backgroundA r hr hne)) hFA
  have hfromB := hasDensity_from_residue_background B q f.activeB (y / q) hBpos f.activeB_mem
    (fun r hr hne => missing_fiber_of_full_section hBpos (f.backgroundB r hr hne)) hFB
  have ha : a = ((SA.card : ℝ) - 1) / q + x / q := hA.unique hfromA
  have hb : b = ((SB.card : ℝ) - 1) / q + y / q := hB.unique hfromB
  have hcardW : (W.card : ℝ) + 1 = (SA.card : ℝ) + SB.card := by
    have hc := f.card_sum
    rw [← residues_add] at hc
    exact_mod_cast hc
  have hcardR : (R.card : ℝ) + 1 = (W.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one hu
  have hcard : (R.card : ℝ) = ((SA.card : ℝ) - 1) + ((SB.card : ℝ) - 1) := by
    linarith
  have hmass : (a + b) - (R.card : ℝ) / q = (x + y) / q := by
    rw [ha, hb, hcard]
    ring
  rw [hmass] at hactiveC
  change HasDensity (residueFiber (A + B) (f.activeA + f.activeB))
    ((x + y) / (f.modulus : ℕ)) at hactiveC
  rw [f.outputFiber_eq hApos hBpos] at hactiveC
  have hsection := section_sum_hasDensity_of_fiber_sum A B f.modulus f.activeA f.activeB
    ((x + y) / (f.modulus : ℕ)) hactiveC
  have hq : (((f.modulus : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast f.modulus.ne_zero
  have hcancel : ((f.modulus : ℕ) : ℝ) * ((x + y) / (f.modulus : ℕ)) = x + y := by
    field_simp
  simpa only [hcancel] using hsection

theorem FiniteFrame.sum_density_iff_active_sections
    {A B : Set ℕ} (f : FiniteFrame A B)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (a b x y : ℝ) (hA : HasDensity A a) (hB : HasDensity B b)
    (hactiveA : HasDensity (residueSection A f.modulus f.activeA) x)
    (hactiveB : HasDensity (residueSection B f.modulus f.activeB) y) :
    HasDensity (A + B) (a + b) ↔
      HasDensity (residueSection A f.modulus f.activeA + residueSection B f.modulus f.activeB)
        (x + y) := by
  constructor
  · intro hC
    exact f.active_sections_sum_hasDensity hApos hBpos a b x y hA hB hC hactiveA hactiveB
  · intro hsum
    have hFA := hasDensity_residueFiber hApos hactiveA
    have hFB := hasDensity_residueFiber hBpos hactiveB
    have hFS := fiber_sum_hasDensity f.modulus f.activeA f.activeB hsum
    apply f.hasDensity_of_active_sum hApos hBpos hA hB hFA hFB
    simpa only [add_div] using hFS

end Erdos335.Proposed
