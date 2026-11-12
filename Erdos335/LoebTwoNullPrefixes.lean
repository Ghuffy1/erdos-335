import Erdos335.FiniteOneBaseline
import Erdos335.LoebWindowBaselines
import Erdos335.LoebWindowMaskBounds

/-!
# The common-prefix-mask obstruction for two null-prefix terminals

Private proof development. Verification status is recorded separately.
The final wrapper exposes the two coarse baseline-mass identities and the
fractional output masses needed to connect it to the two local terminals.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem baseline_strict_of_fractional_total
    (s : ℝ) (h : ℕ+) (n k : ℕ) (x : ℝ) (hx : 0 < x) (hxone : x < 1)
    (hpartial : s * (h : ℕ) = (k : ℝ) + x)
    (hbelow : (n : ℝ) / (h : ℕ) ≤ s) :
    (n : ℝ) / (h : ℕ) < s := by
  have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hnle : (n : ℝ) ≤ (k : ℝ) + x := by
    have hmul := (div_le_iff₀ hh).mp hbelow
    rwa [hpartial] at hmul
  have hnlt : (n : ℝ) < (k : ℝ) + 1 := by linarith
  have hnNat : n < k + 1 := by exact_mod_cast hnlt
  have hnk : n ≤ k := by omega
  apply (div_lt_iff₀ hh).mpr
  rw [hpartial]
  have hnkReal : (n : ℝ) ≤ k := by exact_mod_cast hnk
  linarith

theorem finite_prefix_masks_one_saturated_baseline
    (A B : Set ℕ) (m : ℕ+) (P Q : Finset (ZMod (m : ℕ))) (a b : ℝ)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPR : P ⊆ residues (m : ℕ) A) (hQS : Q ⊆ residues (m : ℕ) B)
    (ha : a = (P.card : ℝ) / (m : ℕ)) (hb : b = (Q.card : ℝ) / (m : ℕ))
    (hgap : a + b < gamma A B)
    (hupper : (((P + residues (m : ℕ) B) ∪ (residues (m : ℕ) A + Q)).card : ℝ) /
      (m : ℕ) ≤ a + b) :
    ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) = a + b ∨
      ((residues (m : ℕ) A + Q).card : ℝ) / (m : ℕ) = a + b := by
  classical
  let R := residues (m : ℕ) A
  let S := residues (m : ℕ) B
  let V := (P + S) ∪ (R + Q)
  have hleft : P + S ⊆ V := Finset.subset_union_left
  have hright : R + Q ⊆ V := Finset.subset_union_right
  have hcore : P + Q ⊆ V :=
    (Finset.add_subset_add (Finset.Subset.refl P) hQS).trans hleft
  have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hmass : (a + b) * (m : ℕ) = (P.card : ℝ) + Q.card := by
    rw [ha, hb]
    rw [add_mul, div_mul_cancel₀ _ hm.ne', div_mul_cancel₀ _ hm.ne']
  have hcardLe : V.card ≤ P.card + Q.card := by
    have hmul : (V.card : ℝ) ≤ (a + b) * (m : ℕ) :=
      (div_le_iff₀ hm).mp hupper
    rw [hmass] at hmul
    exact_mod_cast hmul
  have hcardGe : P.card + Q.card ≤ V.card := by
    by_contra hnot
    have hsmall : V.card < P.card + Q.card := by omega
    have hcover := FiniteKneser.extended_support_sum_subset
      (P := P) (Q := Q) (S := R) (T := S) (U := V)
      hP hQ hcore hright hleft hsmall
    have hgamma := gamma_le_of_residue_sum_subset A B V (hcover.trans hcore)
    exact (not_le_of_gt hgap) (hgamma.trans hupper)
  have hcard : V.card = P.card + Q.card := Nat.le_antisymm hcardLe hcardGe
  have hVmass : (V.card : ℝ) / (m : ℕ) = a + b := by
    rw [hcard, Nat.cast_add, add_div, ← ha, ← hb]
  rcases FiniteKneser.one_baseline_eq_output P Q R S V hP hQ hPR hQS rfl hcard
      with hfull | hfull
  · left
    change ((P + S).card : ℝ) / (m : ℕ) = a + b
    rw [hfull]
    exact hVmass
  · right
    change ((R + Q).card : ℝ) / (m : ℕ) = a + b
    rw [hfull]
    exact hVmass

local instance twoNullPrefixesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

theorem loeb_two_prefix_masks_one_saturated_baseline
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (P Q : Finset (ZMod (m : ℕ)))
    (hPA : ∀ r, actualWindowProfile U hU q m A (fun _ => 0) r =
      if r ∈ P then (1 : ℝ) else 0)
    (hQB : ∀ r, actualWindowProfile U hU q m B (fun _ => 0) r =
      if r ∈ Q then (1 : ℝ) else 0) :
    ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) = a + b ∨
      ((residues (m : ℕ) A + Q).card : ℝ) / (m : ℕ) = a + b := by
  classical
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hPmass : a = (P.card : ℝ) / (m : ℕ) := by
    have h := actual_window_indicator_mass U hU q m hd A (fun _ => 0) P hPA
    rwa [hmA] at h
  have hQmass : b = (Q.card : ℝ) / (m : ℕ) := by
    have h := actual_window_indicator_mass U hU q m hd B (fun _ => 0) Q hQB
    rwa [hmB] at h
  have hP : P.Nonempty := by
    by_contra hnot
    have hempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div] at hPmass
    exact ha.ne' hPmass
  have hQ : Q.Nonempty := by
    by_contra hnot
    have hempty : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div] at hQmass
    exact hb.ne' hQmass
  have hPR : P ⊆ residues (m : ℕ) A := by
    intro r hr
    by_contra hnot
    have hz := actual_window_profile_zero_outside_residues U hU q m hd A (fun _ => 0) r hnot
    change actualWindowProfile U hU q m A (fun _ => 0) r = 0 at hz
    rw [hPA r, if_pos hr] at hz
    norm_num at hz
  have hQS : Q ⊆ residues (m : ℕ) B := by
    intro r hr
    by_contra hnot
    have hz := actual_window_profile_zero_outside_residues U hU q m hd B (fun _ => 0) r hnot
    change actualWindowProfile U hU q m B (fun _ => 0) r = 0 at hz
    rw [hQB r, if_pos hr] at hz
    norm_num at hz
  let V := (P + residues (m : ℕ) B) ∪ (residues (m : ℕ) A + Q)
  have hleft : ∀ r ∈ P + residues (m : ℕ) B,
      actualWindowProfile U hU q m (A + B) (fun _ => 0) r = 1 := by
    intro r hr
    have h := actual_periodic_input_baseline U hU q hq m hd B A (fun _ => 0) P hPA r
      (by simpa only [add_comm] using hr)
    simpa only [add_comm B A] using h
  have hright : ∀ r ∈ residues (m : ℕ) A + Q,
      actualWindowProfile U hU q m (A + B) (fun _ => 0) r = 1 :=
    actual_periodic_input_baseline U hU q hq m hd A B (fun _ => 0) Q hQB
  have hVfull : ∀ r ∈ V, actualWindowProfile U hU q m (A + B) (fun _ => 0) r = 1 := by
    intro r hr
    rcases Finset.mem_union.mp hr with hleft' | hright'
    · exact hleft r hleft'
    · exact hright r hright'
  have hsub := actual_window_full_mask_subset U hU q m hd (A + B) (fun _ => 0) V hVfull
  have hupper : (V.card : ℝ) / (m : ℕ) ≤ a + b := by
    have hle := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    rw [loebMeasure_windowResidueMap_preimage U hU q m hd (fun _ => 0) V,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hmC] at hle
    exact hle
  exact finite_prefix_masks_one_saturated_baseline A B m P Q a b hP hQ hPR hQS
    hPmass hQmass hgap hupper

theorem loeb_two_null_prefix_frames_impossible
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m : ℕ+) (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (P Q : Finset (ZMod (m : ℕ)))
    (hPA : ∀ r, actualWindowProfile U hU q m A (fun _ => 0) r =
      if r ∈ P then (1 : ℝ) else 0)
    (hQB : ∀ r, actualWindowProfile U hU q m B (fun _ => 0) r =
      if r ∈ Q then (1 : ℝ) else 0)
    (hA hB : ℕ+) (nA nB kA kB : ℕ) (xA xB : ℝ)
    (hxA : 0 < xA) (hxAone : xA < 1) (hxB : 0 < xB) (hxBone : xB < 1)
    (hpartialA : (a + b) * (hA : ℕ) = (kA : ℝ) + xA)
    (hpartialB : (a + b) * (hB : ℕ) = (kB : ℝ) + xB)
    (hleftMass : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) = (nA : ℝ) / (hA : ℕ))
    (hrightMass : ((residues (m : ℕ) A + Q).card : ℝ) / (m : ℕ) = (nB : ℝ) / (hB : ℕ)) :
    False := by
  rcases loeb_two_prefix_masks_one_saturated_baseline U hU q hq m hd A B a b ha hb
      hmA hmB hmC hgap P Q hPA hQB with hleft | hright
  · have heq : (nA : ℝ) / (hA : ℕ) = a + b := hleftMass.symm.trans hleft
    have hstrict := baseline_strict_of_fractional_total (a + b) hA nA kA xA
      hxA hxAone hpartialA heq.le
    exact (ne_of_lt hstrict) heq
  · have heq : (nB : ℝ) / (hB : ℕ) = a + b := hrightMass.symm.trans hright
    have hstrict := baseline_strict_of_fractional_total (a + b) hB nB kB xB
      hxB hxBone hpartialB heq.le
    exact (ne_of_lt hstrict) heq

end Erdos335.Loeb

end
