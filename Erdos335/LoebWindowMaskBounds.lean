import Erdos335.WindowResidueRefinement
import Erdos335.LoebShiftedProfileMasks

/-!
# Exact carrier bounds and indicator masks for actual windows
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance windowMaskBoundsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_window_residue_subset
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ) :
    internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ⊆
      windowResidueMap U q h start ⁻¹' (residues (h : ℕ) A : Set _) := by
  intro x hx
  exact actual_residue_of_internal_cyclic_window U q h hd A start x hx

theorem actual_window_residue_capacity
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ) :
    (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal ≤
        ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hle := ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono (actual_window_residue_subset U q h hd A start))
  rw [loebMeasure_windowResidueMap_preimage U hU q h hd,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hle
  exact hle

theorem actual_window_mask_of_indicator_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (R : Finset (ZMod (h : ℕ)))
    (hR : ∀ r, actualWindowProfile U hU q h A start r = if r ∈ R then (1 : ℝ) else 0) :
    internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU] windowResidueMap U q h start ⁻¹' (R : Set _) := by
  rw [windowResidueMap_preimage]
  exact loeb_ae_eq_shifted_mask_of_full_profile U hU q h hd _ (measurable_internalSet U _) R _ hR

theorem actual_window_indicator_mass
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (R : Finset (ZMod (h : ℕ)))
    (hR : ∀ r, actualWindowProfile U hU q h A start r = if r ∈ R then (1 : ℝ) else 0) :
    (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal =
        (R.card : ℝ) / (h : ℕ) := by
  have heq := congrArg ENNReal.toReal
    (measure_congr (actual_window_mask_of_indicator_profile U hU q h hd A start R hR))
  rw [loebMeasure_windowResidueMap_preimage U hU q h hd,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at heq
  exact heq

end Erdos335.Loeb

end
