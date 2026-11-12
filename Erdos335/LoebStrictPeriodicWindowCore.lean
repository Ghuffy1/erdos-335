import Erdos335.LoebWindowBaselines
import Erdos335.LoebWindowMaskBounds
import Erdos335.FiniteNaturalCriticalCore

/-!
# Coarsening the strict baseline of a periodic actual input
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance strictPeriodicWindowCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_strict_periodic_window_core
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (T : Finset (ZMod (m : ℕ)))
    (hT : ∀ r, actualWindowProfile U hU q m B start r = if r ∈ T then (1 : ℝ) else 0)
    (hstrict : ((residues (m : ℕ) A + T).card : ℝ) / (m : ℕ) < a + b) :
    ∃ (h : ℕ+) (S : Finset (ZMod (h : ℕ))),
      (h : ℕ) ∣ (m : ℕ) ∧ S ⊆ residues (h : ℕ) B ∧
      (S + residues (h : ℕ) A).card + 1 = S.card + (residues (h : ℕ) A).card ∧
      (∀ r ∉ S, actualWindowProfile U hU q h B start r = 0) ∧
      (∀ r ∈ S + residues (h : ℕ) A, actualWindowProfile U hU q h (A + B) start r = 1) ∧
      ((S + residues (h : ℕ) A).card : ℝ) < ((h : ℕ) : ℝ) * (a + b) := by
  classical
  let R := residues (m : ℕ) A
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hAmass := actual_window_residue_capacity U hU q m hd A start
  rw [hmA] at hAmass
  have hBmass := actual_window_indicator_mass U hU q m hd B start T hT
  rw [hmB] at hBmass
  have hRne : R.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hc : R.card = 0 := by omega
    change a ≤ (R.card : ℝ) / (m : ℕ) at hAmass
    rw [hc, Nat.cast_zero, zero_div] at hAmass
    linarith
  have hTne : T.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hc : T.card = 0 := by omega
    rw [hc, Nat.cast_zero, zero_div] at hBmass
    linarith
  have hsmall : (T + R).card < T.card + R.card := by
    have hlt : ((T + R).card : ℝ) / (m : ℕ) < ((T.card : ℝ) + R.card) / (m : ℕ) := by
      rw [add_div, ← hBmass]
      have hstrict' : ((T + R).card : ℝ) / (m : ℕ) < a + b := by
        simpa only [R, add_comm] using hstrict
      linarith
    have hc := (div_lt_div_iff_of_pos_right hmpos).mp hlt
    exact_mod_cast hc
  obtain ⟨h, hhm, hcard, hpre, hratio⟩ := exists_finite_natural_critical_core m T R hTne hRne hsmall
  let π := naturalCyclicProjection m h
  let S := T.image π
  have hd' : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := hd.mono fun n hn => dvd_trans hhm hn
  have hRimage : R.image π = residues (h : ℕ) A :=
    residues_image_of_natCast m h π (fun n => naturalCyclicProjection_natCast m h hhm n) A
  have himage : (T + R).image π = S + residues (h : ℕ) A := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_add, Set.image_add, ← Finset.coe_image,
      ← Finset.coe_image, hRimage, Finset.coe_add]
  change ((T + R).image π).card + 1 = S.card + (R.image π).card at hcard
  rw [himage, hRimage] at hcard
  have hSsub : S ⊆ residues (h : ℕ) B := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    have htB : t ∈ residues (m : ℕ) B := by
      by_contra hn
      have hz := actual_window_profile_zero_outside_residues U hU q m hd B start t hn
      change actualWindowProfile U hU q m B start t = 0 at hz
      have ho := hT t
      rw [if_pos ht] at ho
      linarith
    obtain ⟨n, hn, hnt⟩ := mem_residues.mp htB
    apply mem_residues.mpr
    refine ⟨n, hn, ?_⟩
    rw [← hnt, naturalCyclicProjection_natCast m h hhm]
  have hBmask := actual_window_mask_of_indicator_profile U hU q m hd B start T hT
  have hBsub : internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      ≤ᵐ[loebMeasure U hU] windowResidueMap U q h start ⁻¹' (S : Set _) := by
    filter_upwards [hBmask] with x hx hxB
    have ht : windowResidueMap U q m start x ∈ T := Eq.mp hx hxB
    exact Finset.mem_image.mpr ⟨_, ht, windowResidueMap_refinement U q m h start hd hhm x⟩
  have hzero := actual_window_zero_off_mask U hU q h B start S hBsub
  have hpull : windowResidueMap U q h start ⁻¹' (S + residues (h : ℕ) A : Finset _) =
      windowResidueMap U q m start ⁻¹' (T + R : Finset _) := by
    ext x
    change windowResidueMap U q h start x ∈ S + residues (h : ℕ) A ↔
      windowResidueMap U q m start x ∈ T + R
    rw [← himage, ← windowResidueMap_refinement U q m h start hd hhm x]
    exact Iff.of_eq (congrArg (fun V : Set (ZMod (m : ℕ)) => windowResidueMap U q m start x ∈ V) hpre)
  have hfine : ∀ r ∈ T + R, actualWindowProfile U hU q m (A + B) start r = 1 := by
    simpa only [R, add_comm] using actual_periodic_input_baseline U hU q hq m hd A B start T hT
  have hCsub := actual_window_full_mask_subset U hU q m hd (A + B) start (T + R) hfine
  rw [← hpull] at hCsub
  have hfull := actual_window_full_on_mask U hU q h hd' (A + B) start (S + residues (h : ℕ) A) hCsub
  have hdeficit : ((S + residues (h : ℕ) A).card : ℝ) < ((h : ℕ) : ℝ) * (a + b) := by
    have hr : ((S + residues (h : ℕ) A).card : ℝ) / (h : ℕ) < a + b := by
      rw [← himage, hratio]
      simpa only [R, add_comm] using hstrict
    have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
    simpa only [mul_comm] using (div_lt_iff₀ hh).mp hr
  exact ⟨h, S, hhm, hSsub, hcard, hzero, hfull, hdeficit⟩

end Erdos335.Loeb

end
