import Erdos335.LoebSaturatedOutputGap
import Erdos335.LoebPeriodicInputGap
import Erdos335.LoebWindowBaselines

/-!
# Capacity-gap alternatives for periodic actual windows
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance periodicGapAlternativeLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem periodic_output_gap_alternative
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ n : ℕ+, ∀ᶠ s in U, (n : ℕ) ∣ (q s : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B)
    (hcapA : ∀ n : ℕ+, a + δA ≤ ((residues (n : ℕ) A).card : ℝ) / (n : ℕ))
    (hcapB : ∀ n : ℕ+, b + δB ≤ ((residues (n : ℕ) B).card : ℝ) / (n : ℕ))
    (m : ℕ+) (C : Finset (ZMod (m : ℕ)))
    (hC : ∀ r, actualWindowProfile U hU q m (A + B) start r = if r ∈ C then (1 : ℝ) else 0) :
    a + b + δA ≤ gamma A B ∨ a + b + δB ≤ gamma A B := by
  classical
  obtain ⟨P, Q, hPR, hQS, hcard, hPA, hQB, hfill⟩ := periodic_output_window_profiles U hU q hq m (hdiv m)
    A B start a b ha hb hmA hmB hmC hgap C hC
  have hPmass := actual_window_indicator_mass U hU q m (hdiv m) A start P hPA
  have hQmass := actual_window_indicator_mass U hU q m (hdiv m) B start Q hQB
  rw [hmA] at hPmass
  rw [hmB] at hQmass
  have hP : P.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero, zero_div] at hPmass
    linarith
  have hQ : Q.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero, zero_div] at hQmass
    linarith
  have hCmass := actual_window_indicator_mass U hU q m (hdiv m) (A + B) start C hC
  rw [hmC] at hCmass
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hleftSub : P + residues (m : ℕ) B ⊆ C := by rw [← hfill]; exact Finset.subset_union_left
  have hrightSub : residues (m : ℕ) A + Q ⊆ C := by rw [← hfill]; exact Finset.subset_union_right
  by_cases hleft : P + residues (m : ℕ) B = C
  · by_cases hright : residues (m : ℕ) A + Q = C
    · obtain ⟨_, _, _, _, _, _, hA, hB, _, _, _⟩ := local_saturated_output_gap_comparison U hU q hdiv
        A B start a b δA δB hmA hmB hmC hgap hcapA hcapB m P Q C hP hQ hPR hQS hleft hright hcard hPA hQB hC
      exact Or.inl hA
    · have hsmall := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hrightSub, hright⟩)
      have hstrict : ((residues (m : ℕ) A + Q).card : ℝ) / (m : ℕ) < b + a := by
        rw [add_comm b a, hCmass]
        exact (div_lt_div_iff_of_pos_right hmpos).mpr (by exact_mod_cast hsmall)
      have hgammaSwap : gamma B A = gamma A B := by unfold gamma modularCapacity; simp only [add_comm]
      obtain ⟨_, _, _, hA⟩ := local_periodic_input_strict_gap_comparison U hU q hdiv hq B A start b a δB δA
        hb ha hδB hmB hmA (by simpa only [add_comm B A, add_comm b a] using hmC)
        (by simpa only [hgammaSwap, add_comm b a] using hgap) hcapB hcapA m Q hQB hstrict
      exact Or.inl (by simpa only [hgammaSwap, add_comm b a] using hA)
  · have hsmall := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hleftSub, hleft⟩)
    have hstrict : ((residues (m : ℕ) B + P).card : ℝ) / (m : ℕ) < a + b := by
      rw [add_comm (residues (m : ℕ) B) P, hCmass]
      exact (div_lt_div_iff_of_pos_right hmpos).mpr (by exact_mod_cast hsmall)
    obtain ⟨_, _, _, hB⟩ := local_periodic_input_strict_gap_comparison U hU q hdiv hq A B start a b δA δB
      ha hb hδA hmA hmB hmC hgap hcapA hcapB m P hPA hstrict
    exact Or.inr hB

theorem periodic_input_gap_alternative
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ n : ℕ+, ∀ᶠ s in U, (n : ℕ) ∣ (q s : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
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
    (hP : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0) :
    a + b + δA ≤ gamma A B ∨ a + b + δB ≤ gamma A B := by
  classical
  have hmSwap : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b := by
    simpa only [add_comm B A] using hmC
  have hbase := actual_periodic_input_baseline_mass_le U hU q hq m (hdiv m) B A start P hP (a + b) hmSwap
  rcases lt_or_eq_of_le hbase with hstrict | heq
  · obtain ⟨_, _, _, hB⟩ := local_periodic_input_strict_gap_comparison U hU q hdiv hq A B start a b δA δB
      ha hb hδA hmA hmB hmC hgap hcapA hcapB m P hP hstrict
    exact Or.inr hB
  · let C := residues (m : ℕ) B + P
    have hmask := saturated_periodic_input_baseline U hU q hq m (hdiv m) B A start P hP (a + b) hmSwap heq
    have hmask' : internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU] windowResidueMap U q m start ⁻¹' (C : Set _) := by
      simpa only [add_comm B A] using hmask
    have hfull := actual_window_full_on_mask U hU q m (hdiv m) (A + B) start C hmask'.symm.le
    have hzero := actual_window_zero_off_mask U hU q m (A + B) start C hmask'.le
    have hC : ∀ r, actualWindowProfile U hU q m (A + B) start r = if r ∈ C then (1 : ℝ) else 0 := by
      intro r
      by_cases hr : r ∈ C
      · rw [if_pos hr]; exact hfull r hr
      · rw [if_neg hr]; exact hzero r hr
    exact periodic_output_gap_alternative U hU q hdiv hq A B start a b δA δB ha hb hδA hδB
      hmA hmB hmC hgap hcapA hcapB m C hC

end Erdos335.Loeb

end
