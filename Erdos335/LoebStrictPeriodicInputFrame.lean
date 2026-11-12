import Erdos335.LoebStrictPeriodicWindowCore
import Erdos335.LoebLocalDeficitProfiles

/-!
# The finite exceptional frame of a strict periodic-input baseline
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance strictPeriodicInputFrameLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_strict_periodic_input_frame
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
    (hP : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hstrict : ((residues (m : ℕ) B + P).card : ℝ) / (m : ℕ) < a + b) :
    ∃ (h : ℕ+) (S : Finset (ZMod (h : ℕ))) (r t : ZMod (h : ℕ)),
      (h : ℕ) ∣ (m : ℕ) ∧ r ∈ residues (h : ℕ) A ∧ t ∈ residues (h : ℕ) B ∧
      r ∉ S ∧ residues (h : ℕ) A = insert r S ∧
      (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
        (residues (h : ℕ) A).card + (residues (h : ℕ) B).card ∧
      (∀ x, actualWindowProfile U hU q h A start x = if x ∈ S then (1 : ℝ) else 0) ∧
      (∀ y ∈ (residues (h : ℕ) B).erase t, actualWindowProfile U hU q h B start y = 1) ∧
      0 < actualWindowProfile U hU q h B start t ∧ actualWindowProfile U hU q h B start t < 1 ∧
      (residues (h : ℕ) A + residues (h : ℕ) B) \ (S + residues (h : ℕ) B) = {r + t} ∧
      (∀ x ∈ residues (h : ℕ) A, ∀ y ∈ residues (h : ℕ) B,
        x + y = r + t → x = r ∧ y = t) := by
  classical
  have hmC' : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b + a := by
    simpa only [add_comm B A, add_comm b a] using hmC
  have hstrict' : ((residues (m : ℕ) B + P).card : ℝ) / (m : ℕ) < b + a := by
    simpa only [add_comm a b] using hstrict
  obtain ⟨h, S, hhm, hS, hcard, hzero, hfull, hdeficit⟩ := exists_strict_periodic_window_core U hU q hq
    m hd B A start b a hb ha hmB hmA P hP hstrict'
  have hd' : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := hd.mono fun n hn => dvd_trans hhm hn
  have hfull' : ∀ x ∈ S + residues (h : ℕ) B,
      actualWindowProfile U hU q h (A + B) start x = 1 := by
    simpa only [add_comm B A] using hfull
  have hdeficit' : ((S + residues (h : ℕ) B).card : ℝ) < ((h : ℕ) : ℝ) * (a + b) := by
    simpa only [add_comm b a] using hdeficit
  obtain ⟨r, t, hr, ht, hrS, hR, hdiff, hAfull, hBfull, hactive, hactiveLt, hunique⟩ :=
    actual_window_local_deficit_template U hU q hq h hd' A B start a b hmA hmB hmC hgap
      S hS hcard hzero hfull' hdeficit'
  have hAprofile (x : ZMod (h : ℕ)) :
      actualWindowProfile U hU q h A start x = if x ∈ S then (1 : ℝ) else 0 := by
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      exact hAfull x hx
    · rw [if_neg hx]
      exact hzero x hx
  have hAmass := actual_window_indicator_mass U hU q h hd' A start S hAprofile
  rw [hmA] at hAmass
  have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hScard : a * (h : ℕ) = S.card := (eq_div_iff hh.ne').mp hAmass
  have hcardReal : ((S + residues (h : ℕ) B).card : ℝ) + 1 =
      (S.card : ℝ) + (residues (h : ℕ) B).card := by exact_mod_cast hcard
  have hpositive : 0 < actualWindowProfile U hU q h B start t := by
    rw [hactive]
    nlinarith
  have hcoreSub : S + residues (h : ℕ) B ⊆ residues (h : ℕ) A + residues (h : ℕ) B :=
    Finset.add_subset_add hS (Finset.Subset.refl _)
  have hdiffCard := Finset.card_sdiff_of_subset hcoreSub
  rw [hdiff, Finset.card_singleton] at hdiffCard
  have hcoreCard := Finset.card_le_card hcoreSub
  have hRcard : (residues (h : ℕ) A).card = S.card + 1 := by
    rw [hR, Finset.card_insert_of_notMem hrS]
  have hwhole : (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
      (residues (h : ℕ) A).card + (residues (h : ℕ) B).card := by omega
  exact ⟨h, S, r, t, hhm, hr, ht, hrS, hR, hwhole, hAprofile, hBfull,
    hpositive, by simpa only [hactive] using hactiveLt, hdiff, hunique⟩

end Erdos335.Loeb

end
