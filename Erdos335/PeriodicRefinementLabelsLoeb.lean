import Erdos335.PeriodicRefinementLabels
import Erdos335.LoebWindowBaselines
import Erdos335.LoebWindowMaskBounds

/-!
# Actual-window instances of the finite periodic labels

Private proof development. Verification status is recorded separately. The masks and completion are in physical
residue coordinates, and the input supports are the literal integer supports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance periodicRefinementLabelsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

theorem saturated_periodic_mask_determines_partner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (P : Finset (ZMod (m : ℕ)))
    (hPA : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hsaturated : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) = a + b) :
    let Q := PeriodicRefinementLabels.completionMask (residues (m : ℕ) A)
      (P + residues (m : ℕ) B)
    Q ⊆ residues (m : ℕ) B ∧
      (P + residues (m : ℕ) B).card = P.card + Q.card ∧
      ∀ r, actualWindowProfile U hU q m B start r = if r ∈ Q then (1 : ℝ) else 0 := by
  classical
  let V := P + residues (m : ℕ) B
  have hmSwap : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b := by
    simpa only [add_comm B A] using hmC
  have hCmask : internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU] windowResidueMap U q m start ⁻¹' (V : Set _) := by
    have h := saturated_periodic_input_baseline U hU q hq m hd B A start P hPA
      (a + b) hmSwap (by simpa only [add_comm] using hsaturated)
    simpa only [add_comm B A, add_comm (residues (m : ℕ) B) P] using h
  have hCfull := actual_window_full_on_mask U hU q m hd (A + B) start V hCmask.symm.le
  have hCzero := actual_window_zero_off_mask U hU q m (A + B) start V hCmask.le
  have hCprofile : ∀ r, actualWindowProfile U hU q m (A + B) start r =
      if r ∈ V then (1 : ℝ) else 0 := by
    intro r
    by_cases hr : r ∈ V
    · rw [if_pos hr]
      exact hCfull r hr
    · rw [if_neg hr]
      exact hCzero r hr
  obtain ⟨P', Q, hPR, hQS, hcard, hPprofile, hQprofile, hfill⟩ :=
    periodic_output_window_profiles U hU q hq m hd A B start a b ha hb
      hmA hmB hmC hgap V hCprofile
  have hPeq : P' = P := by
    ext r
    have heq := (hPprofile r).symm.trans (hPA r)
    by_cases hr' : r ∈ P' <;> by_cases hr : r ∈ P <;> simp [hr', hr] at heq ⊢
  rw [hPeq] at hPR hcard hfill
  have hP : P.Nonempty := by
    have hmass := actual_window_indicator_mass U hU q m hd A start P hPA
    rw [hmA] at hmass
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty.mp hnot, Finset.card_empty,
      Nat.cast_zero, zero_div] at hmass
    linarith
  have hQ : Q.Nonempty := by
    have hmass := actual_window_indicator_mass U hU q m hd B start Q hQprofile
    rw [hmB] at hmass
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty.mp hnot, Finset.card_empty,
      Nat.cast_zero, zero_div] at hmass
    linarith
  have houtside : ¬residues (m : ℕ) A + residues (m : ℕ) B ⊆ V := by
    intro hsub
    have hbound := gamma_le_of_residue_sum_subset A B V hsub
    rw [show (V.card : ℝ) / (m : ℕ) = a + b from hsaturated] at hbound
    exact not_le_of_gt hgap hbound
  have hRQ : residues (m : ℕ) A + Q ⊆ V := by
    rw [← hfill]
    exact Finset.subset_union_right
  obtain ⟨_, hQeq⟩ := PeriodicRefinementLabels.saturated_partner_eq_completion
    P (residues (m : ℕ) A) (residues (m : ℕ) B) V Q hP hQ hPR
    (Finset.Subset.refl V) hRQ houtside hcard.le
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hQeq] using hQS
  · simpa only [hQeq] using hcard
  · simpa only [hQeq] using hQprofile

theorem periodic_input_masks_have_saturated_baseline
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (P Q : Finset (ZMod (m : ℕ)))
    (hPA : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hQB : ∀ r, actualWindowProfile U hU q m B start r = if r ∈ Q then (1 : ℝ) else 0) :
    ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) = a + b ∨
      ((residues (m : ℕ) A + Q).card : ℝ) / (m : ℕ) = a + b := by
  classical
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hPmass := actual_window_indicator_mass U hU q m hd A start P hPA
  have hQmass := actual_window_indicator_mass U hU q m hd B start Q hQB
  rw [hmA] at hPmass
  rw [hmB] at hQmass
  have hP : P.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty.mp hnot, Finset.card_empty,
      Nat.cast_zero, zero_div] at hPmass
    linarith
  have hQ : Q.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty.mp hnot, Finset.card_empty,
      Nat.cast_zero, zero_div] at hQmass
    linarith
  have hPR : P ⊆ residues (m : ℕ) A := by
    intro r hr
    by_contra hnot
    have hz := actual_window_profile_zero_outside_residues U hU q m hd A start r hnot
    change actualWindowProfile U hU q m A start r = 0 at hz
    rw [hPA r, if_pos hr] at hz
    norm_num at hz
  have hQS : Q ⊆ residues (m : ℕ) B := by
    intro r hr
    by_contra hnot
    have hz := actual_window_profile_zero_outside_residues U hU q m hd B start r hnot
    change actualWindowProfile U hU q m B start r = 0 at hz
    rw [hQB r, if_pos hr] at hz
    norm_num at hz
  let V := (P + residues (m : ℕ) B) ∪ (residues (m : ℕ) A + Q)
  have hleft : ∀ r ∈ P + residues (m : ℕ) B,
      actualWindowProfile U hU q m (A + B) start r = 1 := by
    intro r hr
    have h := actual_periodic_input_baseline U hU q hq m hd B A start P hPA r
      (by simpa only [add_comm] using hr)
    simpa only [add_comm B A] using h
  have hright : ∀ r ∈ residues (m : ℕ) A + Q,
      actualWindowProfile U hU q m (A + B) start r = 1 :=
    actual_periodic_input_baseline U hU q hq m hd A B start Q hQB
  have hVfull : ∀ r ∈ V, actualWindowProfile U hU q m (A + B) start r = 1 := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact hleft r hr
    · exact hright r hr
  have hsub := actual_window_full_mask_subset U hU q m hd (A + B) start V hVfull
  have hbound : (V.card : ℝ) / (m : ℕ) ≤ a + b := by
    have hle := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    rw [loebMeasure_windowResidueMap_preimage U hU q m hd start V,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hmC] at hle
    exact hle
  exact (critical_residue_union_has_full_baseline A B m P Q V a b hP hQ hPR hQS
    rfl hPmass hQmass hbound hgap).2

end Erdos335.Loeb

end
