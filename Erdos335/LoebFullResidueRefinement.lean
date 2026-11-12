import Erdos335.WindowResidueRefinement
import Erdos335.LoebWindowMaskBounds

/-!
# Refining full output background residues
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance fullResidueRefinementLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_window_full_coarse_residues_refine
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ n : ℕ+, ∀ᶠ s in U, (n : ℕ) ∣ (q s : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (h : ℕ+) (R : Finset (ZMod (h : ℕ)))
    (hfull : ∀ r ∈ R, actualWindowProfile U hU q h A start r = 1) :
    ∀ n : ℕ+, (h : ℕ) ∣ (n : ℕ) → ∀ r : ZMod (n : ℕ),
      naturalCyclicProjection n h r ∈ R → r ∈ residues (n : ℕ) A := by
  have hbase := actual_window_full_mask_subset U hU q h (hdiv h) A start R hfull
  intro n hn r hr
  have hsub : windowResidueMap U q n start ⁻¹' {r} ⊆ windowResidueMap U q h start ⁻¹' (R : Set _) := by
    intro x hx
    change windowResidueMap U q n start x = r at hx
    change windowResidueMap U q h start x ∈ R
    rw [← windowResidueMap_refinement U q n h start (hdiv n) hn x, hx]
    exact hr
  have hone : actualWindowProfile U hU q n A start r = 1 := by
    apply loebResidueProfile_one_of_fiber_ae_subset U hU q n (hdiv n)
    rw [← windowResidueMap_fiber]
    exact hsub.eventuallySubset.trans hbase
  by_contra hout
  have hzero := actual_window_profile_zero_outside_residues U hU q n (hdiv n) A start r hout
  change actualWindowProfile U hU q n A start r = 0 at hzero
  rw [hone] at hzero
  norm_num at hzero

theorem actual_window_nonactive_output_full
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun s => (q s : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ s in U, (h : ℕ) ∣ (q s : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (i j : ZMod (h : ℕ))
    (hAfull : ∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1)
    (hBfull : ∀ r ∈ (residues (h : ℕ) B).erase j, actualWindowProfile U hU q h B start r = 1) :
    ∀ r ∈ (residues (h : ℕ) A + residues (h : ℕ) B).erase (i + j),
      actualWindowProfile U hU q h (A + B) start r = 1 := by
  intro r hr
  obtain ⟨hne, hr⟩ := Finset.mem_erase.mp hr
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hr
  apply le_antisymm (loebResidueProfile_le_one U hU q h hd _ _)
  by_cases hxi : x = i
  · have hyj : y ≠ j := by
      intro heq
      exact hne (by rw [hxi, heq])
    obtain ⟨v, hv, hvx⟩ := mem_residues.mp hx
    have hle := actual_window_profile_translate_le U hU q hq h hd B A start v hv y
    change actualWindowProfile U hU q h B start y ≤
      actualWindowProfile U hU q h (B + A) start (y + (v : ZMod (h : ℕ))) at hle
    rw [hBfull y (Finset.mem_erase.mpr ⟨hyj, hy⟩)] at hle
    simpa only [actualWindowProfile, hvx, add_comm B A, add_comm y x] using hle
  · obtain ⟨v, hv, hvy⟩ := mem_residues.mp hy
    have hle := actual_window_profile_translate_le U hU q hq h hd A B start v hv x
    change actualWindowProfile U hU q h A start x ≤
      actualWindowProfile U hU q h (A + B) start (x + (v : ZMod (h : ℕ))) at hle
    rw [hAfull x (Finset.mem_erase.mpr ⟨hxi, hx⟩)] at hle
    simpa only [actualWindowProfile, hvy] using hle

end Erdos335.Loeb

end
