import Erdos335.FiniteExceptionalMass
import Erdos335.LoebActualFiberTranslations
import Erdos335.LoebFullResidueRefinement

/-!
# Equality of the active input and output fiber measures in a null frame
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped BigOperators Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance nullFrameMassLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_window_exceptional_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (i : ZMod (h : ℕ)) (hi : i ∈ residues (h : ℕ) A)
    (hfull : ∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1) :
    actualWindowProfile U hU q h A start i =
      (h : ℕ) * (loebMeasure U hU (internalSet U
        (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal -
          ((residues (h : ℕ) A).card : ℝ) + 1 := by
  have hz : ∀ r ∉ residues (h : ℕ) A, actualWindowProfile U hU q h A start r = 0 := by
    intro r hr
    exact actual_window_profile_zero_outside_residues U hU q h hd A start r hr
  have hm := FiniteProfiles.sum_profile_with_one_exception (residues (h : ℕ) A) i hi
    (actualWindowProfile U hU q h A start) hz hfull
  have hs := sum_shifted_loebResidueProfile U hU q h
    (internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (finiteValue U (fun n => (start n : ZMod (h : ℕ))))
  change (∑ r, actualWindowProfile U hU q h A start r) = _ at hs
  linarith

theorem null_frame_active_measures_equal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (i j : ZMod (h : ℕ))
    (hi : i ∈ residues (h : ℕ) A) (hj : j ∈ residues (h : ℕ) B)
    (ha : a = (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ))
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hcard : (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
      (residues (h : ℕ) A).card + (residues (h : ℕ) B).card)
    (hAfull : ∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1)
    (hBfull : ∀ r ∈ (residues (h : ℕ) B).erase j, actualWindowProfile U hU q h B start r = 1) :
    loebMeasure U hU (actualWindowFiber U q h B start j) =
      loebMeasure U hU (actualWindowFiber U q h (A + B) start (i + j)) := by
  letI : IsProbabilityMeasure (loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU) :=
    isProbabilityMeasure_loebMeasure U hU
  have hCfull := actual_window_nonactive_output_full U hU q hq h hd A B start i j hAfull hBfull
  have hij : i + j ∈ residues (h : ℕ) (A + B) := by
    rw [residues_add]
    exact Finset.add_mem_add hi hj
  have hBprofile := actual_window_exceptional_profile U hU q h hd B start j hj hBfull
  have hCprofile := actual_window_exceptional_profile U hU q h hd (A + B) start (i + j) hij
    (by simpa only [residues_add] using hCfull)
  rw [hmB] at hBprofile
  rw [hmC, residues_add] at hCprofile
  have hcardReal : ((residues (h : ℕ) A + residues (h : ℕ) B).card : ℝ) + 1 =
      ((residues (h : ℕ) A).card : ℝ) + (residues (h : ℕ) B).card := by exact_mod_cast hcard
  have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have haMul : (h : ℕ) * a = ((residues (h : ℕ) A).card : ℝ) - 1 := by
    rw [ha]
    field_simp
  have hp : actualWindowProfile U hU q h B start j =
      actualWindowProfile U hU q h (A + B) start (i + j) := by nlinarith
  have hf (D : Set ℕ) (r : ZMod (h : ℕ)) :
      actualWindowProfile U hU q h D start r =
        (h : ℕ) * (loebMeasure U hU (actualWindowFiber U q h D start r)).toReal := by
    unfold actualWindowFiber
    rw [windowResidueMap_fiber]
    rfl
  rw [hf, hf] at hp
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (mul_left_cancel₀ hh.ne' hp)

end Erdos335.Loeb

end
