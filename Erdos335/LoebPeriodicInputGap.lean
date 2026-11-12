import Erdos335.LiteralExceptionalGap
import Erdos335.LoebFullResidueRefinement
import Erdos335.LoebStrictPeriodicInputFrame

/-!
# The capacity comparison for a strict local periodic-input frame
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance periodicInputGapLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem local_periodic_input_strict_gap_comparison
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ n : ℕ+, ∀ᶠ s in U, (n : ℕ) ∣ (q s : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B)
    (hcapA : ∀ n : ℕ+, a + δA ≤ ((residues (n : ℕ) A).card : ℝ) / (n : ℕ))
    (hcapB : ∀ n : ℕ+, b + δB ≤ ((residues (n : ℕ) B).card : ℝ) / (n : ℕ))
    (m : ℕ+) (P : Finset (ZMod (m : ℕ)))
    (hP : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hstrict : ((residues (m : ℕ) B + P).card : ℝ) / (m : ℕ) < a + b) :
    ∃ h : ℕ+, (h : ℕ) ∣ (m : ℕ) ∧ ((h : ℕ) : ℝ) ≤ 1 / δA ∧ a + b + δB ≤ gamma A B := by
  classical
  obtain ⟨h, S, i, j, hhm, hi, hj, hiS, hRA, hcard, hprofileA, hBfull, _, _, _, _⟩ :=
    loeb_strict_periodic_input_frame U hU q hq m (hdiv m) A B start a b ha hb hmA hmB hmC hgap P hP hstrict
  have hAmass : a = (S.card : ℝ) / (h : ℕ) := by
    have hm := actual_window_indicator_mass U hU q h (hdiv h) A start S hprofileA
    rwa [hmA] at hm
  have haFrame : a = (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ) := by
    rw [hRA, Finset.card_insert_of_notMem hiS, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    exact hAmass
  have hAfull : ∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1 := by
    intro r hr
    obtain ⟨hri, hrA⟩ := Finset.mem_erase.mp hr
    have hrS : r ∈ S := by
      rw [hRA, Finset.mem_insert] at hrA
      exact hrA.resolve_left hri
    rw [hprofileA r, if_pos hrS]
  have hCfull := actual_window_nonactive_output_full U hU q hq h (hdiv h) A B start i j hAfull hBfull
  have hCrefine := actual_window_full_coarse_residues_refine U hU q hdiv (A + B) start h
    ((residues (h : ℕ) A + residues (h : ℕ) B).erase (i + j)) hCfull
  have hcompare := input_gap_le_output_gap_of_full_background A B a b δB h i j hi hj hcard haFrame hCrefine hcapB
  have hhpos : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hδh : δA ≤ (1 : ℝ) / (h : ℕ) := by
    have hc := hcapA h
    rw [haFrame] at hc
    have heq : (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ) + 1 / (h : ℕ) =
        ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by ring
    linarith
  have hindex : ((h : ℕ) : ℝ) ≤ 1 / δA := by
    apply (le_div_iff₀ hδA).mpr
    have hp := (le_div_iff₀ hhpos).mp hδh
    simpa only [mul_comm] using hp
  exact ⟨h, hhm, hindex, hcompare⟩

end Erdos335.Loeb

end
