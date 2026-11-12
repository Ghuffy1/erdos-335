import Erdos335.FiniteSaturatedNaturalFrame
import Erdos335.LoebIndicatorCoarsening
import Erdos335.LiteralExceptionalGap
import Erdos335.LoebFullResidueRefinement

/-!
# Capacity gaps and a bounded period for a saturated local output mask
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance saturatedOutputGapLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem local_saturated_output_gap_comparison
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ n : ℕ+, ∀ᶠ s in U, (n : ℕ) ∣ (q s : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δA δB : ℝ)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B)
    (hcapA : ∀ n : ℕ+, a + δA ≤ ((residues (n : ℕ) A).card : ℝ) / (n : ℕ))
    (hcapB : ∀ n : ℕ+, b + δB ≤ ((residues (n : ℕ) B).card : ℝ) / (n : ℕ))
    (m : ℕ+) (P Q C : Finset (ZMod (m : ℕ))) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPR : P ⊆ residues (m : ℕ) A) (hQS : Q ⊆ residues (m : ℕ) B)
    (hPS : P + residues (m : ℕ) B = C) (hRQ : residues (m : ℕ) A + Q = C)
    (hcard : C.card = P.card + Q.card)
    (hPA : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hQB : ∀ r, actualWindowProfile U hU q m B start r = if r ∈ Q then (1 : ℝ) else 0)
    (hCC : ∀ r, actualWindowProfile U hU q m (A + B) start r = if r ∈ C then (1 : ℝ) else 0) :
    ∃ (h : ℕ+) (P' Q' C' : Finset (ZMod (h : ℕ))),
      (h : ℕ) ∣ (m : ℕ) ∧ ((h : ℕ) : ℝ) ≤ 1 / (gamma A B - (a + b)) ∧
      a + b + δA ≤ gamma A B ∧ a + b + δB ≤ gamma A B ∧
      (∀ r, actualWindowProfile U hU q h A start r = if r ∈ P' then (1 : ℝ) else 0) ∧
      (∀ r, actualWindowProfile U hU q h B start r = if r ∈ Q' then (1 : ℝ) else 0) ∧
      (∀ r, actualWindowProfile U hU q h (A + B) start r = if r ∈ C' then (1 : ℝ) else 0) := by
  classical
  have hCmass : a + b = (C.card : ℝ) / (m : ℕ) := by
    have hm := actual_window_indicator_mass U hU q m (hdiv m) (A + B) start C hCC
    rwa [hmC] at hm
  have houtside : ¬residues (m : ℕ) A + residues (m : ℕ) B ⊆ C := by
    intro hsub
    have hu := gamma_le_of_residue_sum_subset A B C hsub
    rw [← hCmass] at hu
    exact not_le_of_gt hgap hu
  obtain ⟨h, hhm, hpreP, hpreQ, hpreC, hratioP, hratioQ, hratioC, hcard', i, j,
      hiP, hjQ, hRA, hRB, hijC, hRS⟩ := exists_saturated_natural_frame m P Q
    (residues (m : ℕ) A) (residues (m : ℕ) B) C hP hQ hPR hQS hPS hRQ hcard houtside
  let π := naturalCyclicProjection m h
  let P' := P.image π
  let Q' := Q.image π
  let C' := C.image π
  have hAp := actual_indicator_profile_coarsen U hU q m h (hdiv m) hhm A start P hpreP hPA
  have hBp := actual_indicator_profile_coarsen U hU q m h (hdiv m) hhm B start Q hpreQ hQB
  have hCp := actual_indicator_profile_coarsen U hU q m h (hdiv m) hhm (A + B) start C hpreC hCC
  have hRAimage : (residues (m : ℕ) A).image π = residues (h : ℕ) A :=
    residues_image_of_natCast m h π (fun n => naturalCyclicProjection_natCast m h hhm n) A
  have hRBimage : (residues (m : ℕ) B).image π = residues (h : ℕ) B :=
    residues_image_of_natCast m h π (fun n => naturalCyclicProjection_natCast m h hhm n) B
  change (residues (m : ℕ) A).image π = insert i P' at hRA
  change (residues (m : ℕ) B).image π = insert j Q' at hRB
  rw [hRAimage] at hRA
  rw [hRBimage] at hRB
  change ((residues (m : ℕ) A).image π + (residues (m : ℕ) B).image π) = insert (i + j) C' at hRS
  rw [hRAimage, hRBimage] at hRS
  have hi : i ∈ residues (h : ℕ) A := by rw [hRA]; exact Finset.mem_insert_self _ _
  have hj : j ∈ residues (h : ℕ) B := by rw [hRB]; exact Finset.mem_insert_self _ _
  have haFrame : a = (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ) := by
    have hm := actual_window_indicator_mass U hU q h (hdiv h) A start P' hAp
    rw [hmA] at hm
    rw [hRA, Finset.card_insert_of_notMem hiP, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    exact hm
  have hbFrame : b = (((residues (h : ℕ) B).card : ℝ) - 1) / (h : ℕ) := by
    have hm := actual_window_indicator_mass U hU q h (hdiv h) B start Q' hBp
    rw [hmB] at hm
    rw [hRB, Finset.card_insert_of_notMem hjQ, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    exact hm
  have hframeCard : (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
      (residues (h : ℕ) A).card + (residues (h : ℕ) B).card := by
    rw [hRS, Finset.card_insert_of_notMem hijC, hRA, Finset.card_insert_of_notMem hiP,
      hRB, Finset.card_insert_of_notMem hjQ]
    change C'.card = P'.card + Q'.card at hcard'
    change C'.card + 1 + 1 = (P'.card + 1) + (Q'.card + 1)
    omega
  have hbackground : (residues (h : ℕ) A + residues (h : ℕ) B).erase (i + j) = C' := by
    rw [hRS]
    exact Finset.erase_insert hijC
  have hfull : ∀ r ∈ C', actualWindowProfile U hU q h (A + B) start r = 1 := by
    intro r hr
    rw [hCp r, if_pos hr]
  have hfullFine := actual_window_full_coarse_residues_refine U hU q hdiv (A + B) start h C' hfull
  have hgapB := input_gap_le_output_gap_of_full_background A B a b δB h i j hi hj hframeCard
    haFrame (by simpa only [hbackground] using hfullFine) hcapB
  have hgammaSwap : gamma B A = gamma A B := by
    unfold gamma modularCapacity
    simp only [add_comm]
  have hfullSwap : ∀ n : ℕ+, (h : ℕ) ∣ (n : ℕ) → ∀ r : ZMod (n : ℕ),
      naturalCyclicProjection n h r ∈
        (residues (h : ℕ) B + residues (h : ℕ) A).erase (j + i) → r ∈ residues (n : ℕ) (B + A) := by
    simpa only [add_comm, hbackground] using hfullFine
  have hgapA := input_gap_le_output_gap_of_full_background B A b a δA h j i hj hi
    (by simpa only [add_comm, Nat.add_comm] using hframeCard) hbFrame hfullSwap hcapA
  have hsumMass : a + b = (C'.card : ℝ) / (h : ℕ) := by
    have hm := actual_window_indicator_mass U hU q h (hdiv h) (A + B) start C' hCp
    rwa [hmC] at hm
  have hupper : gamma A B ≤ a + b + (1 : ℝ) / (h : ℕ) := by
    have hu := gamma_le_modularCapacity A B h
    change gamma A B ≤ ((residues (h : ℕ) A + residues (h : ℕ) B).card : ℝ) / (h : ℕ) at hu
    rw [hRS, Finset.card_insert_of_notMem hijC, Nat.cast_add, Nat.cast_one, add_div, ← hsumMass] at hu
    exact hu
  have hhpos : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hΔ : 0 < gamma A B - (a + b) := sub_pos.mpr hgap
  have hindex : ((h : ℕ) : ℝ) ≤ 1 / (gamma A B - (a + b)) := by
    apply (le_div_iff₀ hΔ).mpr
    have hbnd : gamma A B - (a + b) ≤ 1 / (h : ℕ) := by linarith
    have hp := (le_div_iff₀ hhpos).mp hbnd
    simpa only [mul_comm] using hp
  exact ⟨h, P', Q', C', hhm, hindex, by simpa only [hgammaSwap, add_comm b a] using hgapA,
    hgapB, hAp, hBp, hCp⟩

end Erdos335.Loeb

end
