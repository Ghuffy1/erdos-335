import Erdos335.PeriodicRefinementLabelClosure
import Erdos335.PeriodicRefinementLabelsLoeb
import Erdos335.LoebStrictPeriodicInputFrame
import Erdos335.LoebNullFrameMass
import Erdos335.FiniteSaturatedNaturalFrame
import Erdos335.LoebWindowMaskBounds
import Erdos335.LoebSaturatedNullFrame
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Actual Loeb frames for finite periodic label closure

Private proof development. Verification status is recorded separately. Fine physical residue equalities are derived
from the exact coarse fiber translation and natural quotient refinement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal BigOperators

noncomputable section

namespace Erdos335.Loeb

local instance labelClosureLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

def actualLocalLabelProfile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b) :
    PeriodicRefinementLabelClosure.LocalProfile (residues (m : ℕ) A) (residues (m : ℕ) B)
      ((m : ℕ) * a) ((m : ℕ) * b) where
  left := actualWindowProfile U hU q m A start
  right := actualWindowProfile U hU q m B start
  output := actualWindowProfile U hU q m (A + B) start
  left_bound := fun r => ⟨loebResidueProfile_nonneg U hU q m _ _,
    loebResidueProfile_le_one U hU q m hd _ _⟩
  right_bound := fun r => ⟨loebResidueProfile_nonneg U hU q m _ _,
    loebResidueProfile_le_one U hU q m hd _ _⟩
  output_bound := fun r => ⟨loebResidueProfile_nonneg U hU q m _ _,
    loebResidueProfile_le_one U hU q m hd _ _⟩
  left_zero := actual_window_profile_zero_outside_residues U hU q m hd A start
  right_zero := actual_window_profile_zero_outside_residues U hU q m hd B start
  left_mass := by
    have h := sum_shifted_loebResidueProfile U hU q m
      (internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
      (finiteValue U (fun n => (start n : ZMod (m : ℕ))))
    change (∑ r, actualWindowProfile U hU q m A start r) = _ at h
    rwa [hmA] at h
  right_mass := by
    have h := sum_shifted_loebResidueProfile U hU q m
      (internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
      (finiteValue U (fun n => (start n : ZMod (m : ℕ))))
    change (∑ r, actualWindowProfile U hU q m B start r) = _ at h
    rwa [hmB] at h
  output_mass := by
    have h := sum_shifted_loebResidueProfile U hU q m
      (internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
      (finiteValue U (fun n => (start n : ZMod (m : ℕ))))
    change (∑ r, actualWindowProfile U hU q m (A + B) start r) = _ at h
    rw [hmC] at h
    exact h.trans (by ring)
  literal_left := by
    intro r v hv
    obtain ⟨n, hn, hnv⟩ := mem_residues.mp hv
    have h := actual_window_profile_translate_le U hU q hq m hd A B start n hn r
    change actualWindowProfile U hU q m A start r ≤
      actualWindowProfile U hU q m (A + B) start (r + (n : ZMod (m : ℕ))) at h
    simpa only [hnv] using h
  literal_right := by
    intro r hr v
    obtain ⟨n, hn, hnr⟩ := mem_residues.mp hr
    have h := actual_window_profile_translate_le U hU q hq m hd B A start n hn v
    change actualWindowProfile U hU q m B start v ≤
      actualWindowProfile U hU q m (B + A) start (v + (n : ZMod (m : ℕ))) at h
    simpa only [hnr, add_comm B A, add_comm v r] using h

theorem literal_card_gap_at_modulus
    (A B : Set ℕ) (a b : ℝ) (m : ℕ+) (hgap : a + b < gamma A B) :
    (m : ℕ) * a + (m : ℕ) * b < ((residues (m : ℕ) A + residues (m : ℕ) B).card : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hcapacity := gamma_le_modularCapacity A B m
  change gamma A B ≤ ((residues (m : ℕ) A + residues (m : ℕ) B).card : ℝ) / (m : ℕ) at hcapacity
  have h := (lt_div_iff₀ hmpos).mp (hgap.trans_le hcapacity)
  nlinarith

theorem actual_physical_indicator_refines
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m h : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (hhm : (h : ℕ) ∣ (m : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (R : Finset (ZMod (h : ℕ)))
    (hR : ∀ r, actualWindowProfile U hU q h A start r = if r ∈ R then (1 : ℝ) else 0) :
    ∀ r, actualWindowProfile U hU q m A start r =
      if naturalCyclicProjection m h r ∈ R then (1 : ℝ) else 0 := by
  classical
  have hdh : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := hdm.mono fun _ hn => dvd_trans hhm hn
  let T := Finset.univ.filter (fun r : ZMod (m : ℕ) => naturalCyclicProjection m h r ∈ R)
  have hcoarse := actual_window_mask_of_indicator_profile U hU q h hdh A start R hR
  have hpre : windowResidueMap U q h start ⁻¹' (R : Set _) =
      windowResidueMap U q m start ⁻¹' (T : Set _) := by
    ext x
    change windowResidueMap U q h start x ∈ R ↔ windowResidueMap U q m start x ∈ T
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [windowResidueMap_refinement U q m h start hdm hhm]
  rw [hpre] at hcoarse
  have hfull := actual_window_full_on_mask U hU q m hdm A start T hcoarse.symm.le
  have hzero := actual_window_zero_off_mask U hU q m A start T hcoarse.le
  intro r
  by_cases hr : r ∈ T
  · have hp := hfull r hr
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using
      (show actualWindowProfile U hU q m A start r = if r ∈ T then (1 : ℝ) else 0 by
        rw [if_pos hr]; exact hp)
  · have hp := hzero r hr
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using
      (show actualWindowProfile U hU q m A start r = if r ∈ T then (1 : ℝ) else 0 by
        rw [if_neg hr]; exact hp)

theorem actual_full_profile_refines
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m h : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (hhm : (h : ℕ) ∣ (m : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (r : ZMod (m : ℕ))
    (hfull : actualWindowProfile U hU q h A start (naturalCyclicProjection m h r) = 1) :
    actualWindowProfile U hU q m A start r = 1 := by
  classical
  have hdh : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := hdm.mono fun _ hn => dvd_trans hhm hn
  have hsub := actual_window_full_mask_subset U hU q h hdh A start
    ({naturalCyclicProjection m h r} : Finset (ZMod (h : ℕ)))
    (by intro s hs; simpa only [Finset.mem_singleton.mp hs] using hfull)
  apply loebResidueProfile_one_of_fiber_ae_subset U hU q m hdm
  rw [← windowResidueMap_fiber]
  have hfiber : windowResidueMap U q m start ⁻¹' {r} ⊆
      windowResidueMap U q h start ⁻¹' ({naturalCyclicProjection m h r} : Set _) := by
    intro x hx
    change windowResidueMap U q h start x = naturalCyclicProjection m h r
    rw [← windowResidueMap_refinement U q m h start hdm hhm x,
      show windowResidueMap U q m start x = r from hx]
  apply hfiber.eventuallySubset.trans
  simpa only [Finset.coe_singleton] using hsub

theorem fine_fiber_translate_of_coarse
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m h : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (hhm : (h : ℕ) ∣ (m : ℕ)) (X Y : Set ℕ) (start : ℕ → ℕ)
    (u : ℕ) (i : ZMod (h : ℕ)) (r : ZMod (m : ℕ))
    (hr : naturalCyclicProjection m h r = i)
    (hcoarse : productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
      actualWindowFiber U q h X start i =ᵐ[loebMeasure U hU]
        actualWindowFiber U q h Y start (i + (u : ZMod (h : ℕ)))) :
    productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
      actualWindowFiber U q m X start r =ᵐ[loebMeasure U hU]
        actualWindowFiber U q m Y start (r + (u : ZMod (m : ℕ))) := by
  filter_upwards [hcoarse] with x hx
  apply propext
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyh : y ∈ actualWindowFiber U q h X start i := by
      refine ⟨hy.1, ?_⟩
      change windowResidueMap U q h start y = i
      rw [← windowResidueMap_refinement U q m h start hdm hhm y,
        show windowResidueMap U q m start y = r from hy.2, hr]
    have hyt := (Iff.of_eq hx).mp ⟨y, hyh, rfl⟩
    refine ⟨hyt.1, ?_⟩
    change windowResidueMap U q m start
      (productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) + y) = _
    rw [windowResidueMap_nat_translate U q m hdm start u y,
      show windowResidueMap U q m start y = r from hy.2]
  · intro hxy
    have hxh : x ∈ actualWindowFiber U q h Y start (i + (u : ZMod (h : ℕ))) := by
      refine ⟨hxy.1, ?_⟩
      change windowResidueMap U q h start x = _
      rw [← windowResidueMap_refinement U q m h start hdm hhm x,
        show windowResidueMap U q m start x = r + (u : ZMod (m : ℕ)) from hxy.2,
        map_add, hr, naturalCyclicProjection_natCast m h hhm]
    obtain ⟨y, hy, hyx⟩ := (Iff.of_eq hx).mpr hxh
    refine ⟨y, ⟨hy.1, ?_⟩, hyx⟩
    have hv := hxy.2
    change windowResidueMap U q m start x = r + (u : ZMod (m : ℕ)) at hv
    rw [← hyx] at hv
    change windowResidueMap U q m start
      (productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) + y) =
        r + (u : ZMod (m : ℕ)) at hv
    rw [windowResidueMap_nat_translate U q m hdm start u y] at hv
    exact add_right_cancel hv

theorem fine_profile_eq_of_coarse_fiber_translate
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m h : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (hhm : (h : ℕ) ∣ (m : ℕ)) (X Y : Set ℕ) (start : ℕ → ℕ)
    (u : ℕ) (i : ZMod (h : ℕ)) (r : ZMod (m : ℕ))
    (hr : naturalCyclicProjection m h r = i)
    (hcoarse : productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
      actualWindowFiber U q h X start i =ᵐ[loebMeasure U hU]
        actualWindowFiber U q h Y start (i + (u : ZMod (h : ℕ)))) :
    actualWindowProfile U hU q m Y start (r + (u : ZMod (m : ℕ))) =
      actualWindowProfile U hU q m X start r := by
  have heq := fine_fiber_translate_of_coarse U hU q m h hdm hhm X Y start u i r hr hcoarse
  have hmass : loebMeasure U hU (actualWindowFiber U q m X start r) =
      loebMeasure U hU (actualWindowFiber U q m Y start (r + (u : ZMod (m : ℕ)))) := by
    calc
      _ = loebMeasure U hU (productProjection (U : Filter ℕ)
          (fun n => (u : ZMod (q n : ℕ))) +ᵥ actualWindowFiber U q m X start r) :=
        (loebMeasure_image_add_left U hU _ _).symm
      _ = _ := measure_congr heq
  have hf (Z : Set ℕ) (s : ZMod (m : ℕ)) : actualWindowProfile U hU q m Z start s =
      (m : ℕ) * (loebMeasure U hU (actualWindowFiber U q m Z start s)).toReal := by
    unfold actualWindowFiber
    rw [windowResidueMap_fiber]
    rfl
  rw [hf, hf, hmass]

theorem actual_null_frame_indicator_at_multiple
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m h : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (hhm : (h : ℕ) ∣ (m : ℕ)) (A B : Set ℕ) (start : ℕ → ℕ) (a : ℝ)
    (hframe : ActualWindowNullFrame U hU q h A B start a)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a) :
    ∃ P : Finset (ZMod (m : ℕ)),
      ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0 := by
  classical
  have hdh : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := hdm.mono fun _ hn => dvd_trans hhm hn
  obtain ⟨i, j, hi, hj, ha, hcard, hfullA, hfullB⟩ := hframe
  let R := (residues (h : ℕ) A).erase i
  have hzero : actualWindowProfile U hU q h A start i = 0 := by
    rw [actual_window_exceptional_profile U hU q h hdh A start i hi hfullA, hmA, ha]
    have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
    field_simp [hh]
    <;> ring
  have hprofile : ∀ r, actualWindowProfile U hU q h A start r = if r ∈ R then (1 : ℝ) else 0 := by
    intro r
    by_cases hr : r ∈ R
    · rw [if_pos hr]
      exact hfullA r hr
    · rw [if_neg hr]
      by_cases hri : r = i
      · simpa only [hri] using hzero
      · apply actual_window_profile_zero_outside_residues U hU q h hdh A start r
        intro hrA
        exact hr (Finset.mem_erase.mpr ⟨hri, hrA⟩)
  refine ⟨Finset.univ.filter (fun r : ZMod (m : ℕ) => naturalCyclicProjection m h r ∈ R), ?_⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    actual_physical_indicator_refines U hU q m h hdm hhm A start R hprofile

theorem actual_bounded_null_frame_indicator
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ m : ℕ+, ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (D : ℕ) (h : ℕ+) (hbound : (h : ℕ) ≤ D)
    (A B : Set ℕ) (start : ℕ → ℕ) (a : ℝ)
    (hframe : ActualWindowNullFrame U hU q h A B start a)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a) :
    let m : ℕ+ := ⟨D.factorial, Nat.factorial_pos D⟩
    ∃ P : Finset (ZMod (m : ℕ)),
      ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0 := by
  dsimp only
  exact actual_null_frame_indicator_at_multiple U hU q
    ⟨D.factorial, Nat.factorial_pos D⟩ h (hdiv _)
    (Nat.dvd_factorial h.pos hbound) A B start a hframe hmA

theorem actual_strict_right_coarse_frame
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (Q : Finset (ZMod (m : ℕ)))
    (hQ : ∀ r, actualWindowProfile U hU q m B start r = if r ∈ Q then (1 : ℝ) else 0)
    (hstrict : ((residues (m : ℕ) A + Q).card : ℝ) / (m : ℕ) < a + b) :
    let p := actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC
    ∃ (h : ℕ+) (T : Finset (ZMod (h : ℕ))) (i j : ZMod (h : ℕ)),
      (h : ℕ) ∣ (m : ℕ) ∧ i ∈ residues (h : ℕ) A ∧ j ∈ residues (h : ℕ) B ∧
      j ∉ T ∧ residues (h : ℕ) B = insert j T ∧
      (residues (h : ℕ) B + residues (h : ℕ) A).card + 1 =
        (residues (h : ℕ) B).card + (residues (h : ℕ) A).card ∧
      (∀ r, actualWindowProfile U hU q h B start r = if r ∈ T then (1 : ℝ) else 0) ∧
      (∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1) ∧
      0 < actualWindowProfile U hU q h A start i ∧ actualWindowProfile U hU q h A start i < 1 ∧
      (∀ v ∈ residues (m : ℕ) B \ Q, naturalCyclicProjection m h v = j) ∧
      ∃ frame : PeriodicRefinementLabelClosure.StrictRightFrame p Q,
        frame.active = (residues (m : ℕ) A).filter (fun r => naturalCyclicProjection m h r = i) := by
  classical
  dsimp only
  have hgammaSwap : gamma B A = gamma A B := by
    unfold gamma modularCapacity
    simp only [add_comm]
  have hmSwap : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b + a := by
    simpa only [add_comm B A, add_comm b a] using hmC
  obtain ⟨h, T, j, i, hhm, hj, hi, hjT, hBsupport, hcard, hBprofile, hAfull,
      hApositive, hApartial, hdiff, hunique⟩ :=
    loeb_strict_periodic_input_frame U hU q hq m hdm B A start b a hb ha hmB hmA hmSwap
      (by simpa only [hgammaSwap, add_comm b a] using hgap) Q hQ
      (by simpa only [add_comm b a] using hstrict)
  have hdh : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := hdm.mono fun _ hn => dvd_trans hhm hn
  let π := naturalCyclicProjection m h
  let I := (residues (m : ℕ) A).filter (fun r => π r = i)
  have hClass : ∀ v ∈ residues (m : ℕ) B \ Q, π v = j := by
    intro v hv
    obtain ⟨hvB, hvQ⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨u, hu, huv⟩ := mem_residues.mp hvB
    have hvCoarse : π v ∈ residues (h : ℕ) B := by
      refine mem_residues.mpr ⟨u, hu, ?_⟩
      rw [← naturalCyclicProjection_natCast m h hhm u, huv]
    have hvNotT : π v ∉ T := by
      intro hvT
      have hp := actual_physical_indicator_refines U hU q m h hdm hhm B start T hBprofile v
      rw [hQ v, if_neg hvQ, if_pos hvT] at hp
      norm_num at hp
    rw [hBsupport, Finset.mem_insert] at hvCoarse
    exact hvCoarse.resolve_right hvNotT
  have hBmass : b = (((residues (h : ℕ) B).card : ℝ) - 1) / (h : ℕ) := by
    have hm := actual_window_indicator_mass U hU q h hdh B start T hBprofile
    rw [hmB] at hm
    rw [hBsupport, Finset.card_insert_of_notMem hjT, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right]
    exact hm
  have hBfull : ∀ r ∈ (residues (h : ℕ) B).erase j, actualWindowProfile U hU q h B start r = 1 := by
    intro r hr
    obtain ⟨hrj, hrB⟩ := Finset.mem_erase.mp hr
    rw [hBsupport, Finset.mem_insert] at hrB
    have hrT := hrB.resolve_left hrj
    rw [hBprofile r, if_pos hrT]
  have hmass := null_frame_active_measures_equal U hU q hq h hdh B A start b a j i
    hj hi hBmass hmA hmSwap hcard hBfull hAfull
  let frame : PeriodicRefinementLabelClosure.StrictRightFrame
      (actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC) Q := {
    active := I
    active_subset := fun r hr => (Finset.mem_filter.mp hr).1
    background_full := by
      intro r hr
      obtain ⟨hrA, hrI⟩ := Finset.mem_sdiff.mp hr
      have hrNotActive : π r ≠ i := by
        intro heq
        exact hrI (Finset.mem_filter.mpr ⟨hrA, heq⟩)
      obtain ⟨u, hu, hur⟩ := mem_residues.mp hrA
      have hrCoarse : π r ∈ residues (h : ℕ) A := by
        refine mem_residues.mpr ⟨u, hu, ?_⟩
        rw [← naturalCyclicProjection_natCast m h hhm u, hur]
      exact actual_full_profile_refines U hU q m h hdm hhm A start r
        (hAfull _ (Finset.mem_erase.mpr ⟨hrNotActive, hrCoarse⟩))
    active_translation := by
      intro v hv r hr
      have hvj := hClass v hv
      obtain ⟨u, hu, huv⟩ := mem_residues.mp (Finset.mem_sdiff.mp hv).1
      have huj : (u : ZMod (h : ℕ)) = j := by
        have hp := naturalCyclicProjection_natCast m h hhm u
        rw [huv] at hp
        exact hp.symm.trans hvj
      have heq := actual_window_fiber_equal_translate U hU q hq h hdh B A start u hu i
        (by simpa only [huj] using hmass)
      have heq' : productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
          actualWindowFiber U q h A start i =ᵐ[loebMeasure U hU]
            actualWindowFiber U q h (A + B) start (i + (u : ZMod (h : ℕ))) := by
        simpa only [add_comm B A, add_comm (u : ZMod (h : ℕ)) i] using heq
      have hf := fine_profile_eq_of_coarse_fiber_translate U hU q m h hdm hhm A (A + B)
        start u i r (Finset.mem_filter.mp hr).2 heq'
      change actualWindowProfile U hU q m (A + B) start (r + v) =
        actualWindowProfile U hU q m A start r
      simpa only [huv] using hf
  }
  exact ⟨h, T, i, j, hhm, hi, hj, hjT, hBsupport, hcard, hBprofile,
    hAfull, hApositive, hApartial, hClass, frame, rfl⟩

theorem saturated_fine_extras_outside
    (m : ℕ+) (P Q R S V : Finset (ZMod (m : ℕ)))
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hPR : P ⊆ R) (hQS : Q ⊆ S)
    (hPS : P + S = V) (hRQ : R + Q = V)
    (hcard : V.card = P.card + Q.card) (houtside : ¬R + S ⊆ V) :
    ∀ r ∈ R \ P, ∀ v ∈ S \ Q, r + v ∉ V := by
  classical
  obtain ⟨h, hhm, hpreP, hpreQ, hpreV, _, _, _, _, i, j,
      hiP, hjQ, hR, hS, hij, hsum⟩ :=
    exists_saturated_natural_frame m P Q R S V hP hQ hPR hQS hPS hRQ hcard houtside
  let π := naturalCyclicProjection m h
  intro r hr v hv hmem
  obtain ⟨hrR, hrP⟩ := Finset.mem_sdiff.mp hr
  obtain ⟨hvS, hvQ⟩ := Finset.mem_sdiff.mp hv
  have hrImage : π r ∈ R.image π := Finset.mem_image.mpr ⟨r, hrR, rfl⟩
  have hvImage : π v ∈ S.image π := Finset.mem_image.mpr ⟨v, hvS, rfl⟩
  have hrNotImage : π r ∉ P.image π := by
    intro hin
    apply hrP
    change r ∈ (P : Set _)
    rw [← hpreP]
    exact hin
  have hvNotImage : π v ∉ Q.image π := by
    intro hin
    apply hvQ
    change v ∈ (Q : Set _)
    rw [← hpreQ]
    exact hin
  rw [hR, Finset.mem_insert] at hrImage
  rw [hS, Finset.mem_insert] at hvImage
  have hri : π r = i := hrImage.resolve_right hrNotImage
  have hvj : π v = j := hvImage.resolve_right hvNotImage
  have hImage : π (r + v) ∈ V.image π := Finset.mem_image.mpr ⟨r + v, hmem, rfl⟩
  rw [map_add, hri, hvj] at hImage
  exact hij hImage

theorem actual_saturated_label_frame
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (P Q : Finset (ZMod (m : ℕ)))
    (hP : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hQ : ∀ r, actualWindowProfile U hU q m B start r = if r ∈ Q then (1 : ℝ) else 0)
    (hPsat : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) = a + b)
    (hQsat : ((residues (m : ℕ) A + Q).card : ℝ) / (m : ℕ) = a + b) :
    PeriodicRefinementLabelClosure.LabelFrame
      (actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC)
      (.both P Q) := by
  classical
  let R := residues (m : ℕ) A
  let S := residues (m : ℕ) B
  let V := P + S
  have hmSwap : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b := by
    simpa only [add_comm B A] using hmC
  have hmask : internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU] windowResidueMap U q m start ⁻¹' (V : Set _) := by
    have h := saturated_periodic_input_baseline U hU q hq m hdm B A start P hP
      (a + b) hmSwap (by simpa only [add_comm] using hPsat)
    simpa only [V, S, add_comm B A, add_comm (residues (m : ℕ) B) P] using h
  have hCfull := actual_window_full_on_mask U hU q m hdm (A + B) start V hmask.symm.le
  have hCzero := actual_window_zero_off_mask U hU q m (A + B) start V hmask.le
  have hRQsub : R + Q ⊆ V := by
    intro r hr
    have hone := actual_periodic_input_baseline U hU q hq m hdm A B start Q hQ r hr
    by_contra hout
    rw [hCzero r hout] at hone
    norm_num at hone
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hRQcard : (R + Q).card = V.card := by
    have heq : (((R + Q).card : ℝ) / (m : ℕ)) = (V.card : ℝ) / (m : ℕ) :=
      hQsat.trans hPsat.symm
    exact_mod_cast (div_left_inj' hmpos.ne').mp heq
  have hRQ : R + Q = V := Finset.eq_of_subset_of_card_le hRQsub hRQcard.ge
  have hAmass := actual_window_indicator_mass U hU q m hdm A start P hP
  have hBmass := actual_window_indicator_mass U hU q m hdm B start Q hQ
  rw [hmA] at hAmass
  rw [hmB] at hBmass
  have hPne : P.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty.mp hnot, Finset.card_empty, Nat.cast_zero, zero_div] at hAmass
    linarith
  have hQne : Q.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty.mp hnot, Finset.card_empty, Nat.cast_zero, zero_div] at hBmass
    linarith
  have hPR : P ⊆ R := PeriodicRefinementLabelClosure.left_mask_subset
    (actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC) P hP
  have hQS : Q ⊆ S := PeriodicRefinementLabelClosure.right_mask_subset
    (actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC) Q hQ
  have hcard : V.card = P.card + Q.card := by
    have heq : (V.card : ℝ) / (m : ℕ) = ((P.card + Q.card : ℕ) : ℝ) / (m : ℕ) := by
      rw [hPsat, hAmass, hBmass, Nat.cast_add, add_div]
    exact_mod_cast (div_left_inj' hmpos.ne').mp heq
  have houtside : ¬R + S ⊆ V := by
    intro hsub
    have hbound := gamma_le_of_residue_sum_subset A B V hsub
    rw [show (V.card : ℝ) / (m : ℕ) = a + b from hPsat] at hbound
    exact not_le_of_gt hgap hbound
  have hforbidden := saturated_fine_extras_outside m P Q R S V hPne hQne hPR hQS rfl hRQ hcard houtside
  intro r hr v hv
  exact hCzero (r + v) (hforbidden r hr v hv)

private theorem local_label_profile_ext
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {R S : Finset G} {a b : ℝ}
    (p q : PeriodicRefinementLabelClosure.LocalProfile R S a b)
    (hleft : p.left = q.left) (hright : p.right = q.right) (hout : p.output = q.output) : p = q := by
  cases p
  cases q
  cases hleft
  cases hright
  cases hout
  rfl

theorem actual_strict_right_label_frame
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (Q : Finset (ZMod (m : ℕ)))
    (hQ : ∀ r, actualWindowProfile U hU q m B start r = if r ∈ Q then (1 : ℝ) else 0)
    (hstrict : ((residues (m : ℕ) A + Q).card : ℝ) / (m : ℕ) < a + b) :
    PeriodicRefinementLabelClosure.LabelFrame
      (actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC) (.right Q) := by
  obtain ⟨h, T, i, j, _, _, _, _, _, _, _, _, _, _, _, frame, _⟩ :=
    actual_strict_right_coarse_frame U hU q hq m hdm A B start a b ha hb hmA hmB hmC hgap Q hQ hstrict
  exact ⟨frame⟩

theorem actual_strict_left_label_frame
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (P : Finset (ZMod (m : ℕ)))
    (hP : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hstrict : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) < a + b) :
    PeriodicRefinementLabelClosure.LabelFrame
      (actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC) (.left P) := by
  have hgammaSwap : gamma B A = gamma A B := by
    unfold gamma modularCapacity
    simp only [add_comm]
  have hmSwap : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b + a := by
    simpa only [add_comm B A, add_comm b a] using hmC
  let p := actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC
  obtain ⟨frame⟩ :=
    actual_strict_right_label_frame U hU q hq m hdm B A start b a hb ha hmB hmA hmSwap
      (by simpa only [hgammaSwap, add_comm b a] using hgap) P hP
      (by simpa only [add_comm] using hstrict)
  change Nonempty (PeriodicRefinementLabelClosure.StrictRightFrame p.swap P)
  refine ⟨{
    active := frame.active
    active_subset := frame.active_subset
    background_full := frame.background_full
    active_translation := ?_
  }⟩
  intro v hv r hr
  have h := frame.active_translation v hv r hr
  change actualWindowProfile U hU q m (B + A) start (r + v) =
    actualWindowProfile U hU q m B start r at h
  change actualWindowProfile U hU q m (A + B) start (r + v) =
    actualWindowProfile U hU q m B start r
  simpa only [add_comm B A] using h

theorem actual_periodic_profile_has_label
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B)
    (hperiodic :
      (∃ P : Finset (ZMod (m : ℕ)), ∀ r, actualWindowProfile U hU q m A start r =
        if r ∈ P then (1 : ℝ) else 0) ∨
      (∃ Q : Finset (ZMod (m : ℕ)), ∀ r, actualWindowProfile U hU q m B start r =
        if r ∈ Q then (1 : ℝ) else 0)) :
    let p := actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC
    ∃ label : PeriodicRefinementLabelClosure.LocalLabel (ZMod (m : ℕ)),
      PeriodicRefinementLabelClosure.HasLabel p label ∧
        PeriodicRefinementLabelClosure.LabelFrame p label := by
  classical
  let p := actualLocalLabelProfile U hU q hq m hdm A B start a b hmA hmB hmC
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have scale_lt (V : Finset (ZMod (m : ℕ)))
      (hV : (V.card : ℝ) / (m : ℕ) < a + b) :
      (V.card : ℝ) < (m : ℕ) * a + (m : ℕ) * b := by
    have h := (div_lt_iff₀ hmpos).mp hV
    nlinarith
  have scale_eq (V : Finset (ZMod (m : ℕ)))
      (hV : (V.card : ℝ) / (m : ℕ) = a + b) :
      (V.card : ℝ) = (m : ℕ) * a + (m : ℕ) * b := by
    have h := (div_eq_iff hmpos.ne').mp hV
    nlinarith
  have hmBA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b := by
    simpa only [add_comm B A] using hmC
  have hmSwap : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b + a := by
    simpa only [add_comm b a] using hmBA
  have hgammaSwap : gamma B A = gamma A B := by
    unfold gamma modularCapacity
    simp only [add_comm]
  rcases hperiodic with ⟨P, hP⟩ | ⟨Q, hQ⟩
  · have hbaseA : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) ≤ a + b := by
      simpa only [add_comm] using actual_periodic_input_baseline_mass_le
        U hU q hq m hdm B A start P hP (a + b) hmBA
    rcases lt_or_eq_of_le hbaseA with hstrictA | hsatA
    · refine ⟨.left P, ⟨hP, scale_lt _ hstrictA⟩, ?_⟩
      exact actual_strict_left_label_frame U hU q hq m hdm A B start a b ha hb
        hmA hmB hmC hgap P hP hstrictA
    · let Q := PeriodicRefinementLabels.completionMask (residues (m : ℕ) A)
        (P + residues (m : ℕ) B)
      have hPartner := saturated_periodic_mask_determines_partner U hU q hq m hdm A B start a b
        ha hb hmA hmB hmC hgap P hP hsatA
      have hQ : ∀ r, actualWindowProfile U hU q m B start r = if r ∈ Q then (1 : ℝ) else 0 :=
        hPartner.2.2
      have hbaseB := actual_periodic_input_baseline_mass_le U hU q hq m hdm A B start Q hQ
        (a + b) hmC
      rcases lt_or_eq_of_le hbaseB with hstrictB | hsatB
      · refine ⟨.right Q, ⟨hQ, scale_lt _ hstrictB⟩, ?_⟩
        exact actual_strict_right_label_frame U hU q hq m hdm A B start a b ha hb
          hmA hmB hmC hgap Q hQ hstrictB
      · refine ⟨.both P Q, ⟨hP, hQ, scale_eq _ hsatA, scale_eq _ hsatB⟩, ?_⟩
        exact actual_saturated_label_frame U hU q hq m hdm A B start a b ha hb
          hmA hmB hmC hgap P Q hP hQ hsatA hsatB
  · have hbaseB := actual_periodic_input_baseline_mass_le U hU q hq m hdm A B start Q hQ
      (a + b) hmC
    rcases lt_or_eq_of_le hbaseB with hstrictB | hsatB
    · refine ⟨.right Q, ⟨hQ, scale_lt _ hstrictB⟩, ?_⟩
      exact actual_strict_right_label_frame U hU q hq m hdm A B start a b ha hb
        hmA hmB hmC hgap Q hQ hstrictB
    · let P := PeriodicRefinementLabels.completionMask (residues (m : ℕ) B)
        (Q + residues (m : ℕ) A)
      have hPartner := saturated_periodic_mask_determines_partner U hU q hq m hdm B A start b a
        hb ha hmB hmA hmSwap (by simpa only [hgammaSwap, add_comm b a] using hgap) Q hQ
        (by simpa only [add_comm] using hsatB)
      have hP : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0 :=
        hPartner.2.2
      have hbaseA : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) ≤ a + b := by
        simpa only [add_comm] using actual_periodic_input_baseline_mass_le
          U hU q hq m hdm B A start P hP (a + b) hmBA
      rcases lt_or_eq_of_le hbaseA with hstrictA | hsatA
      · refine ⟨.left P, ⟨hP, scale_lt _ hstrictA⟩, ?_⟩
        exact actual_strict_left_label_frame U hU q hq m hdm A B start a b ha hb
          hmA hmB hmC hgap P hP hstrictA
      · refine ⟨.both P Q, ⟨hP, hQ, scale_eq _ hsatA, scale_eq _ hsatB⟩, ?_⟩
        exact actual_saturated_label_frame U hU q hq m hdm A B start a b ha hb
          hmA hmB hmC hgap P Q hP hQ hsatA hsatB

theorem actual_bounded_null_frame_has_label
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ m : ℕ+, ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (D : ℕ) (h : ℕ+) (hbound : (h : ℕ) ≤ D)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B)
    (hframe : ActualWindowNullFrame U hU q h A B start a ∨ ActualWindowNullFrame U hU q h B A start b) :
    let m : ℕ+ := ⟨D.factorial, Nat.factorial_pos D⟩
    let p := actualLocalLabelProfile U hU q hq m (hdiv m) A B start a b hmA hmB hmC
    ∃ label : PeriodicRefinementLabelClosure.LocalLabel (ZMod (m : ℕ)),
      PeriodicRefinementLabelClosure.HasLabel p label ∧
        PeriodicRefinementLabelClosure.LabelFrame p label := by
  dsimp only
  apply actual_periodic_profile_has_label U hU q hq
    ⟨D.factorial, Nat.factorial_pos D⟩ (hdiv _) A B start a b ha hb hmA hmB hmC hgap
  rcases hframe with hframe | hframe
  · exact Or.inl (actual_bounded_null_frame_indicator U hU q hdiv D h hbound A B start a hframe hmA)
  · exact Or.inr (actual_bounded_null_frame_indicator U hU q hdiv D h hbound B A start b hframe hmB)

end Erdos335.Loeb

namespace Erdos335.PeriodicRefinementLabelClosure

theorem hasLabel_unique
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (first second : LocalLabel G) (hfirst : HasLabel p first) (hsecond : HasLabel p second) :
    first = second := by
  cases first with
  | right Q =>
      exact (label_eq_right_of_indicator p ha hb hgap second hsecond Q hfirst.1 hfirst.2).symm
  | both P Q =>
      exact (label_eq_both_of_indicators p second hsecond P Q hfirst.1 hfirst.2.1
        hfirst.2.2.1 hfirst.2.2.2).symm
  | left P =>
      have heq := label_eq_right_of_indicator p.swap hb ha
        (by simpa only [add_comm] using hgap) second.swap hsecond.swap P hfirst.1
        (by simpa only [add_comm] using hfirst.2)
      have hback := congrArg LocalLabel.swap heq
      have hresult : second = .left P := by
        rw [LocalLabel.swap_swap] at hback
        exact hback
      exact hresult.symm

end Erdos335.PeriodicRefinementLabelClosure

end
