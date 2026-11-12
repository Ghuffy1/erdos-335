import Erdos335.WindowResidueRefinement
import Erdos335.LoebWindowMaskBounds

/-!
# Coarsening a full residue mask without losing the physical window phase
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance indicatorCoarseningLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_indicator_profile_coarsen
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m h : ℕ+) (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ)) (hhm : (h : ℕ) ∣ (m : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (P : Finset (ZMod (m : ℕ)))
    (hpre : (naturalCyclicProjection m h) ⁻¹'
      (P.image (naturalCyclicProjection m h) : Set (ZMod (h : ℕ))) = P)
    (hprofile : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0) :
    ∀ r, actualWindowProfile U hU q h A start r =
      if r ∈ P.image (naturalCyclicProjection m h) then (1 : ℝ) else 0 := by
  classical
  let Q := P.image (naturalCyclicProjection m h)
  have hd' : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := hd.mono fun n hn => dvd_trans hhm hn
  have hsets : windowResidueMap U q m start ⁻¹' (P : Set _) =
      windowResidueMap U q h start ⁻¹' (Q : Set _) := by
    rw [← hpre]
    ext x
    change naturalCyclicProjection m h (windowResidueMap U q m start x) ∈ Q ↔
      windowResidueMap U q h start x ∈ Q
    rw [windowResidueMap_refinement U q m h start hd hhm]
  have hmask := (actual_window_mask_of_indicator_profile U hU q m hd A start P hprofile).trans
    (Filter.EventuallyEq.of_eq hsets)
  have hfull := actual_window_full_on_mask U hU q h hd' A start Q hmask.symm.le
  have hzero := actual_window_zero_off_mask U hU q h A start Q hmask.le
  intro r
  by_cases hr : r ∈ Q
  · rw [if_pos hr]
    exact hfull r hr
  · rw [if_neg hr]
    exact hzero r hr

end Erdos335.Loeb

end
