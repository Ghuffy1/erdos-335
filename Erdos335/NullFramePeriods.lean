import Erdos335.DensitySubsetPeriods
import Erdos335.Singleton

/-!
# Ordinary translate coverage and difference periods in a null-active frame
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem FiniteFrame.null_left_translate_coverage
    {A B : Set ℕ} (f : FiniteFrame A B)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) (a b x : ℝ)
    (hdA : HasDensity A a) (hdB : HasDensity B b) (hdC : HasDensity (A + B) (a + b))
    (hzero : HasDensity (residueSection A f.modulus f.activeA) 0)
    (hactive : HasDensity (residueSection B f.modulus f.activeB) x)
    (u : ℕ) (hu : u ∈ residueFiber A f.activeA) :
    DensityEquivalent (shift (residueFiber B f.activeB) u)
      (residueFiber (A + B) (f.activeA + f.activeB)) := by
  let q := f.modulus
  have hAfiber : HasDensity (residueFiber A f.activeA) 0 := by
    simpa only [zero_div] using hasDensity_residueFiber hA hzero
  have hBfiber : HasDensity (residueFiber B f.activeB) (x / (q : ℕ)) :=
    hasDensity_residueFiber hB hactive
  have hAD : a = (((residues (q : ℕ) A).card : ℝ) - 1) / (q : ℕ) := by
    have hh := hasDensity_from_residue_background A q f.activeA 0 hA f.activeA_mem
      (fun r hr hri => missing_fiber_of_full_section hA (f.backgroundA r hr hri)) hAfiber
    simpa only [add_zero] using hdA.unique hh
  have hBD : b = (((residues (q : ℕ) B).card : ℝ) - 1) / (q : ℕ) + x / (q : ℕ) :=
    hdB.unique (hasDensity_from_residue_background B q f.activeB (x / (q : ℕ)) hB f.activeB_mem
      (fun r hr hrj => missing_fiber_of_full_section hB (f.backgroundB r hr hrj)) hBfiber)
  have huC : f.activeA + f.activeB ∈ residues (q : ℕ) (A + B) := by
    rw [residues_add]
    exact Finset.add_mem_add f.activeA_mem f.activeB_mem
  have hCfiber := active_fiber_density_of_full_background (A + B) q (f.activeA + f.activeB)
    (a + b) (sumset_positive hA hB) hdC huC
    (fun r hr hri => f.output_background hA hB hr hri)
  have hcard : ((residues (q : ℕ) (A + B)).card : ℝ) + 1 =
      ((residues (q : ℕ) A).card : ℝ) + (residues (q : ℕ) B).card := by
    rw [residues_add]
    exact_mod_cast f.card_sum
  have hcoefficient : a + b - (((residues (q : ℕ) (A + B)).card : ℝ) - 1) / (q : ℕ) =
      x / (q : ℕ) := by
    rw [hAD, hBD]
    have hq : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
    field_simp
    linarith
  rw [hcoefficient] at hCfiber
  apply densityEquivalent_of_subset_same_density _ _ (x / (q : ℕ)) _ (hBfiber.shift u) hCfiber
  rintro z ⟨v, hv, rfl⟩
  have hur : (u : ZMod (q : ℕ)) = f.activeA := by simpa only [Finset.mem_singleton] using hu.2.2
  have hvr : (v : ZMod (q : ℕ)) = f.activeB := by simpa only [Finset.mem_singleton] using hv.2.2
  refine ⟨⟨u, hu.1, v, hv.1, Nat.add_comm u v⟩, ?_, ?_⟩
  · have hu0 := hu.2.1
    have hv0 := hv.2.1
    change 0 < v + u
    omega
  · simp only [Nat.cast_add, hur, hvr, add_comm, Finset.mem_singleton]

theorem FiniteFrame.null_left_active_difference_period
    {A B : Set ℕ} (f : FiniteFrame A B)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) (a b x : ℝ)
    (hdA : HasDensity A a) (hdB : HasDensity B b) (hdC : HasDensity (A + B) (a + b))
    (hzero : HasDensity (residueSection A f.modulus f.activeA) 0)
    (hactive : HasDensity (residueSection B f.modulus f.activeB) x)
    (u v : ℕ) (hu : u ∈ residueFiber A f.activeA) (hv : v ∈ residueFiber A f.activeA)
    (huv : u ≤ v) :
    DensityEquivalent (shift (residueFiber B f.activeB) (v - u)) (residueFiber B f.activeB) := by
  have hleft := f.null_left_translate_coverage hA hB a b x hdA hdB hdC hzero hactive u hu
  have hright := f.null_left_translate_coverage hA hB a b x hdA hdB hdC hzero hactive v hv
  exact period_of_equal_translates _ u v huv (hleft.trans hright.symm)

end Erdos335.Proposed
