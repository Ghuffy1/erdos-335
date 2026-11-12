import Erdos335.LoebProfileBounds
import Erdos335.LoebPeriodicWindowProfiles

/-!
# Transferring quotient cores to physical window residues
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance shiftedWindowCoresLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem finset_translate_add {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S T : Finset G) (z : G) :
    S.image (fun r => r + z) + T = (S + T).image (fun r => r + z) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨r + t, Finset.add_mem_add hr ht, by abel⟩
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Finset.mem_add.mp hu
    exact Finset.mem_add.mpr ⟨s + z, Finset.mem_image.mpr ⟨s, hs, rfl⟩, t, ht, by abel⟩

theorem actual_window_core_image_subset
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hD : D ⊆ internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (S : Finset (ZMod (h : ℕ)))
    (hS : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) '' D = (S : Set _)) :
    S.image (fun r => r + finiteValue U (fun n => (start n : ZMod (h : ℕ)))) ⊆ residues (h : ℕ) A := by
  intro r hr
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
  have hsD : s ∈ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) '' D := hS.symm ▸ hs
  obtain ⟨x, hx, rfl⟩ := hsD
  exact actual_residue_of_internal_cyclic_window U q h hd A start x (hD hx)

theorem actual_window_profile_zero_of_core
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (A : Set ℕ) (start : ℕ → ℕ)
    (D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hD : D =ᵐ[loebMeasure U hU]
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (S : Finset (ZMod (h : ℕ)))
    (hS : D ⊆ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (S : Set _)) :
    ∀ r ∉ S.image (fun r => r + finiteValue U (fun n => (start n : ZMod (h : ℕ)))),
      actualWindowProfile U hU q h A start r = 0 := by
  classical
  intro r hr
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  have hn : r - z ∉ S := by
    intro hs
    exact hr (Finset.mem_image.mpr ⟨r - z, hs, sub_add_cancel _ _⟩)
  unfold actualWindowProfile
  rw [← loebResidueProfile_eq_of_ae U hU q h D _ hD]
  exact loebResidueProfile_zero_of_subset U hU q h D S hS (r - z) hn

theorem actual_window_profile_full_of_core
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (R : Finset (ZMod (h : ℕ)))
    (hR : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) ≤ᵐ[loebMeasure U hU]
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    ∀ r ∈ R.image (fun r => r + finiteValue U (fun n => (start n : ZMod (h : ℕ)))),
      actualWindowProfile U hU q h A start r = 1 := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
  unfold actualWindowProfile
  rw [add_sub_cancel_right]
  apply loebResidueProfile_one_of_fiber_ae_subset U hU q h hd
  have hsub : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {t} ⊆
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) := by
    intro x hx
    change finiteQuotient U (fun n => naturalCyclicProjection (q n) h) x = t at hx
    change finiteQuotient U (fun n => naturalCyclicProjection (q n) h) x ∈ R
    simpa only [hx] using ht
  exact hsub.eventuallySubset.trans hR

end Erdos335.Loeb

end
