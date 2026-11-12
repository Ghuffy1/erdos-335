import Erdos335.LoebSaturatedOutputGap
import Erdos335.LoebStrictPeriodicInputFrame

/-!
# Null-frame data retained by periodic-input reductions

Private proof development. Verification status is recorded separately.
The frame predicate exposes exactly the local data consumed by the existing
integer-period and finite-translate coverage theorems.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance saturatedNullFrameLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

def ActualWindowNullFrame
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (A B : Set ℕ) (start : ℕ → ℕ) (a : ℝ) : Prop :=
  ∃ i j : ZMod (h : ℕ), i ∈ residues (h : ℕ) A ∧ j ∈ residues (h : ℕ) B ∧
    a = (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ) ∧
    (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
      (residues (h : ℕ) A).card + (residues (h : ℕ) B).card ∧
    (∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1) ∧
    (∀ r ∈ (residues (h : ℕ) B).erase j, actualWindowProfile U hU q h B start r = 1)

theorem strict_periodic_input_has_bounded_null_frame
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δA : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (m : ℕ+) (P : Finset (ZMod (m : ℕ)))
    (hP : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hstrict : ((residues (m : ℕ) B + P).card : ℝ) / (m : ℕ) < a + b) :
    ∃ h : ℕ+, (h : ℕ) ∣ (m : ℕ) ∧ ((h : ℕ) : ℝ) ≤ 1 / δA ∧
      ActualWindowNullFrame U hU q h A B start a := by
  classical
  obtain ⟨h, S, i, j, hhm, hi, hj, hiS, hRA, hcard, hPA, hBfull, _, _, _, _⟩ :=
    loeb_strict_periodic_input_frame U hU q hq m (hdiv m) A B start a b ha hb
      hmA hmB hmC hgap P hP hstrict
  have hAmass : a = (S.card : ℝ) / (h : ℕ) := by
    have hm := actual_window_indicator_mass U hU q h (hdiv h) A start S hPA
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
    rw [hPA r, if_pos hrS]
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
  exact ⟨h, hhm, hindex, i, j, hi, hj, haFrame, hcard, hAfull, hBfull⟩

theorem saturated_output_has_bounded_null_frames
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B)
    (m : ℕ+) (P Q C : Finset (ZMod (m : ℕ))) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPR : P ⊆ residues (m : ℕ) A) (hQS : Q ⊆ residues (m : ℕ) B)
    (hPS : P + residues (m : ℕ) B = C) (hRQ : residues (m : ℕ) A + Q = C)
    (hcard : C.card = P.card + Q.card)
    (hPA : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hQB : ∀ r, actualWindowProfile U hU q m B start r = if r ∈ Q then (1 : ℝ) else 0)
    (hCC : ∀ r, actualWindowProfile U hU q m (A + B) start r = if r ∈ C then (1 : ℝ) else 0) :
    ∃ h : ℕ+, (h : ℕ) ∣ (m : ℕ) ∧
      ((h : ℕ) : ℝ) ≤ 1 / (gamma A B - (a + b)) ∧
      ActualWindowNullFrame U hU q h A B start a ∧
      ActualWindowNullFrame U hU q h B A start b := by
  classical
  have hCmass : a + b = (C.card : ℝ) / (m : ℕ) := by
    have hm := actual_window_indicator_mass U hU q m (hdiv m) (A + B) start C hCC
    rwa [hmC] at hm
  have houtside : ¬residues (m : ℕ) A + residues (m : ℕ) B ⊆ C := by
    intro hsub
    have hu := gamma_le_of_residue_sum_subset A B C hsub
    rw [← hCmass] at hu
    exact not_le_of_gt hgap hu
  obtain ⟨h, hhm, hpreP, hpreQ, hpreC, _, _, _, hcard', i, j,
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
  change (residues (m : ℕ) A).image π + (residues (m : ℕ) B).image π = insert (i + j) C' at hRS
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
  have hAfull : ∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1 := by
    intro r hr
    have hrP : r ∈ P' := by
      rw [hRA] at hr
      simp only [Finset.mem_erase, Finset.mem_insert] at hr
      exact hr.2.resolve_left hr.1
    rw [hAp r, if_pos hrP]
  have hBfull : ∀ r ∈ (residues (h : ℕ) B).erase j, actualWindowProfile U hU q h B start r = 1 := by
    intro r hr
    have hrQ : r ∈ Q' := by
      rw [hRB] at hr
      simp only [Finset.mem_erase, Finset.mem_insert] at hr
      exact hr.2.resolve_left hr.1
    rw [hBp r, if_pos hrQ]
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
  refine ⟨h, hhm, hindex, ⟨i, j, hi, hj, haFrame, hframeCard, hAfull, hBfull⟩, ?_⟩
  exact ⟨j, i, hj, hi, hbFrame, by simpa only [add_comm, Nat.add_comm] using hframeCard,
    hBfull, hAfull⟩

theorem periodic_input_has_bounded_null_frame
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
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
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (m : ℕ+) (P : Finset (ZMod (m : ℕ)))
    (hP : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0) :
    ∃ h : ℕ+, (h : ℕ) ∣ (m : ℕ) ∧
      ((h : ℕ) : ℝ) ≤ max (1 / δA) (max (1 / δB) (1 / (gamma A B - (a + b)))) ∧
      (ActualWindowNullFrame U hU q h A B start a ∨
        ActualWindowNullFrame U hU q h B A start b) := by
  classical
  let bound := max (1 / δA) (max (1 / δB) (1 / (gamma A B - (a + b))))
  have hswap : gamma B A = gamma A B := by unfold gamma modularCapacity; simp only [add_comm]
  have hmSwap : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b + a := by
    simpa only [add_comm B A, add_comm b a] using hmC
  have strictA (R : Finset (ZMod (m : ℕ)))
      (hR : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ R then (1 : ℝ) else 0)
      (hstrict : ((residues (m : ℕ) B + R).card : ℝ) / (m : ℕ) < a + b) :
      ∃ h : ℕ+, (h : ℕ) ∣ (m : ℕ) ∧ ((h : ℕ) : ℝ) ≤ bound ∧
        (ActualWindowNullFrame U hU q h A B start a ∨
          ActualWindowNullFrame U hU q h B A start b) := by
    obtain ⟨h, hd, hbound, hframe⟩ := strict_periodic_input_has_bounded_null_frame U hU q
      hdiv hq A B start a b δA ha hb hδA hmA hmB hmC hgap hcapA m R hR hstrict
    exact ⟨h, hd, hbound.trans (le_max_left _ _), Or.inl hframe⟩
  have strictB (R : Finset (ZMod (m : ℕ)))
      (hR : ∀ r, actualWindowProfile U hU q m B start r = if r ∈ R then (1 : ℝ) else 0)
      (hstrict : ((residues (m : ℕ) A + R).card : ℝ) / (m : ℕ) < a + b) :
      ∃ h : ℕ+, (h : ℕ) ∣ (m : ℕ) ∧ ((h : ℕ) : ℝ) ≤ bound ∧
        (ActualWindowNullFrame U hU q h A B start a ∨
          ActualWindowNullFrame U hU q h B A start b) := by
    obtain ⟨h, hd, hbound, hframe⟩ := strict_periodic_input_has_bounded_null_frame U hU q
      hdiv hq B A start b a δB hb ha hδB hmB hmA hmSwap
      (by simpa only [hswap, add_comm b a] using hgap) hcapB m R hR
      (by simpa only [add_comm b a] using hstrict)
    exact ⟨h, hd, hbound.trans ((le_max_left _ _).trans (le_max_right _ _)), Or.inr hframe⟩
  have hmBA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b := by
    simpa only [add_comm B A] using hmC
  have hbase := actual_periodic_input_baseline_mass_le U hU q hq m (hdiv m)
    B A start P hP (a + b) hmBA
  rcases lt_or_eq_of_le hbase with hstrict | heq
  · exact strictA P hP hstrict
  · let C := residues (m : ℕ) B + P
    have hmaskBA := saturated_periodic_input_baseline U hU q hq m (hdiv m)
      B A start P hP (a + b) hmBA heq
    have hmask : internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU] windowResidueMap U q m start ⁻¹' (C : Set _) := by
      simpa only [add_comm B A] using hmaskBA
    have hfull := actual_window_full_on_mask U hU q m (hdiv m) (A + B) start C hmask.symm.le
    have hzero := actual_window_zero_off_mask U hU q m (A + B) start C hmask.le
    have hCprofile : ∀ r, actualWindowProfile U hU q m (A + B) start r =
        if r ∈ C then (1 : ℝ) else 0 := by
      intro r
      by_cases hr : r ∈ C
      · rw [if_pos hr]; exact hfull r hr
      · rw [if_neg hr]; exact hzero r hr
    obtain ⟨R, S, hRA, hSB, hcard, hR, hS, hfill⟩ :=
      periodic_output_window_profiles U hU q hq m (hdiv m) A B start a b ha hb
        hmA hmB hmC hgap C hCprofile
    have hCmass : a + b = (C.card : ℝ) / (m : ℕ) := by
      have hm := actual_window_indicator_mass U hU q m (hdiv m) (A + B) start C hCprofile
      rwa [hmC] at hm
    have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
    by_cases hleft : R + residues (m : ℕ) B = C
    · by_cases hright : residues (m : ℕ) A + S = C
      · have hRmass := actual_window_indicator_mass U hU q m (hdiv m) A start R hR
        have hSmass := actual_window_indicator_mass U hU q m (hdiv m) B start S hS
        rw [hmA] at hRmass
        rw [hmB] at hSmass
        have hRnonempty : R.Nonempty := by
          by_contra hn
          rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero, zero_div] at hRmass
          linarith
        have hSnonempty : S.Nonempty := by
          by_contra hn
          rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero, zero_div] at hSmass
          linarith
        obtain ⟨h, hd, hbound, hframe, _⟩ := saturated_output_has_bounded_null_frames U hU q
          hdiv A B start a b hmA hmB hmC hgap m R S C hRnonempty hSnonempty
          hRA hSB hleft hright hcard hR hS hCprofile
        exact ⟨h, hd, hbound.trans ((le_max_right _ _).trans (le_max_right _ _)), Or.inl hframe⟩
      · have hsub : residues (m : ℕ) A + S ⊆ C := by
          rw [← hfill]
          exact Finset.subset_union_right
        have hcardlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hright⟩)
        apply strictB S hS
        rw [hCmass]
        exact (div_lt_div_iff_of_pos_right hmpos).mpr (by exact_mod_cast hcardlt)
    · have hsub : R + residues (m : ℕ) B ⊆ C := by
        rw [← hfill]
        exact Finset.subset_union_left
      have hcardlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hleft⟩)
      apply strictA R hR
      rw [add_comm (residues (m : ℕ) B) R, hCmass]
      exact (div_lt_div_iff_of_pos_right hmpos).mpr (by exact_mod_cast hcardlt)

end Erdos335.Loeb

end
