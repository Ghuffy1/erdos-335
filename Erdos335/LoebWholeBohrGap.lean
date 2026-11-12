import Erdos335.LoebWholeBohrProfiles
import Erdos335.LoebWholeBohrCarrier
import Erdos335.LoebPositiveOutputCarrier

/-!
# Capacity gaps in the whole-pair Bohr alternative
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal Classical

noncomputable section

namespace Erdos335.Loeb

local instance wholeBohrGapLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem whole_bohr_gap_formulas
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (hB : B.Nonempty) (start : ℕ → ℕ) (a b : ℝ) (hb : 0 < b)
    (W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (E : ℕ → Set ℕ)
    (hWA : W =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hEsub : ∀ᶠ n in U, E n ⊆ B) (hexhaust : ∀ v ∈ B, ∀ᶠ n in U, v ∈ E n)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmE : (loebMeasure U hU (internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b)
    (d : InternalBohrPairData U hU q W
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hSm : MeasurableSet (W + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hfull : loebMeasure U hU (W + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) =
      loebMeasure U hU W + loebMeasure U hU (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hmodelC : W + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    a = d.left_length / (d.modulus : ℕ) ∧ b = d.right_length / (d.modulus : ℕ) ∧
    gamma A B = 1 / (d.modulus : ℕ) ∧
    (∀ k : ℕ+, a + (1 - d.left_length) / (d.modulus : ℕ) ≤
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ)) ∧
    (∀ k : ℕ+, b + (1 - d.right_length) / (d.modulus : ℕ) ≤
      ((residues (k : ℕ) B).card : ℝ) / (k : ℕ)) := by
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let m := d.modulus
  let φ := finiteQuotient U d.residue
  let i := φ d.left_anchor + finiteValue U (fun n => (start n : ZMod (m : ℕ)))
  let j := φ d.right_anchor
  let u := φ (d.left_anchor + d.right_anchor) + finiteValue U (fun n => (start n : ZMod (m : ℕ)))
  have hmassA : a = d.left_length / (m : ℕ) := by
    calc
      a = (loebMeasure U hU W).toReal :=
        ((congrArg ENNReal.toReal (measure_congr hWA)).trans hmA).symm
      _ = _ := (congrArg ENNReal.toReal (measure_congr d.left_model)).trans
        (internalBohrCoset_measure_toReal U hU q m (hdiv m) d.residue
          (d.natural_residue.mono fun n hn => hn.2) d.character d.character_surjective
          d.left_anchor d.left_start d.left_length d.left_positive.le
          (by linarith [d.length_sum_lt_one, d.right_positive]))
  have hmassB : b = d.right_length / (m : ℕ) := by
    calc
      b = (loebMeasure U hU P).toReal := hmE.symm
      _ = _ := (congrArg ENNReal.toReal (measure_congr d.right_model)).trans
        (internalBohrCoset_measure_toReal U hU q m (hdiv m) d.residue
          (d.natural_residue.mono fun n hn => hn.2) d.character d.character_surjective
          d.right_anchor d.right_start d.right_length d.right_positive.le
          (by linarith [d.length_sum_lt_one, d.left_positive]))
  have hRB : residues (m : ℕ) B = {j} := whole_bohr_prefix_carrier U hU q W B E hB hEsub hexhaust d
  have hid : naturalCyclicProjection m m = AddMonoidHom.id (ZMod (m : ℕ)) := by
    ext r
    rw [naturalCyclicProjection_val m m dvd_rfl, ZMod.natCast_zmod_val]
    rfl
  have hCprofile (r : ZMod (m : ℕ)) : actualWindowProfile U hU q m (A + B) start r =
      if r = u then d.left_length + d.right_length else 0 := by
    have hp := whole_bohr_output_physical_profile U hU q W P d
      hSm hfull (A + B) start hmodelC m (hdiv m) dvd_rfl r
    change actualWindowProfile U hU q m (A + B) start r =
      (if naturalCyclicProjection m m r = u then d.left_length + d.right_length else 0) at hp
    simpa only [hid, AddMonoidHom.id_apply] using hp
  have hpartner (r : ZMod (m : ℕ)) (hr : r ∈ residues (m : ℕ) B) :
      0 < actualWindowProfile U hU q m B start r := by
    have hl := actual_window_profile_ge_total_sub_card U hU q m (hdiv m) B start b hmB r hr
    rw [hRB, Finset.card_singleton] at hl
    norm_num only [Nat.cast_one, sub_self, sub_zero] at hl
    exact (mul_pos (by exact_mod_cast m.pos) hb).trans_le hl
  have hcarrier : residues (m : ℕ) (A + B) = {u} :=
    actual_output_literal_carrier U hU q hq m (hdiv m) A B start {u} hpartner
      (fun r hr => by
        have hp := hCprofile r
        rw [if_neg (by simpa only [Finset.mem_singleton] using hr)] at hp
        exact hp)
      (fun r hr => by
        have hr' : r = u := Finset.mem_singleton.mp hr
        rw [hCprofile r, if_pos hr']
        exact add_pos d.left_positive d.right_positive)
  have hgamma : gamma A B = 1 / (m : ℕ) := by
    have hg := gamma_eq_of_positive_window_refinements U hU q hdiv A B start m {u} hcarrier (by
      intro h hmh r hr
      have hp := whole_bohr_output_physical_profile U hU q W P d hSm hfull (A + B) start hmodelC h
        (hdiv h) hmh r
      rw [if_pos (Finset.mem_singleton.mp hr)] at hp
      rw [hp]
      exact add_pos d.left_positive d.right_positive)
    simpa only [Finset.card_singleton, Nat.cast_one] using hg
  have hcapA := actual_window_capacity_ge_of_positive_refinements U hU q hdiv A start m {i} (by
    intro h hmh r hr
    have hp := whole_bohr_left_physical_profile U hU q W P d A start hWA h (hdiv h) hmh r
    rw [if_pos (Finset.mem_singleton.mp hr)] at hp
    rw [hp]
    exact d.left_positive)
  have hcapB := literal_prefix_capacity_ge_of_positive_refinements U hU q hdiv B E hEsub hexhaust m {j} (by
    intro h hmh r hr
    have hp := (d.residue_profiles h (hdiv h) hmh).2 r
    rw [if_pos (Finset.mem_singleton.mp hr)] at hp
    rw [hp]
    exact d.right_positive)
  refine ⟨hmassA, hmassB, hgamma, ?_, ?_⟩
  · intro k
    have heq : a + (1 - d.left_length) / (m : ℕ) = 1 / (m : ℕ) := by
      rw [hmassA]
      ring
    rw [heq]
    simpa only [Finset.card_singleton, Nat.cast_one] using hcapA k
  · intro k
    have heq : b + (1 - d.right_length) / (m : ℕ) = 1 / (m : ℕ) := by
      rw [hmassB]
      ring
    rw [heq]
    simpa only [Finset.card_singleton, Nat.cast_one] using hcapB k

end Erdos335.Loeb

end
