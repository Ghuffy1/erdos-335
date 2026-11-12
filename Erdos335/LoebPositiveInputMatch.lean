import Erdos335.LoebPhysicalBohrInputs
import Erdos335.LoebProfileCapacity
import Erdos335.FinitePartialMass

/-!
# Matching a positive window model to a literal prefix mass
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal Classical

noncomputable section

namespace Erdos335.Loeb

local instance positiveInputMatchLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_positive_window_literal_support_of_mass
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (W P : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) W P)
    (d : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U d.residue).ker)
    (A : Set ℕ) (start : ℕ → ℕ) (a y : ℝ)
    (hmodel : W =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hmass : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hy : 0 < y) (hy1 : y < 1)
    (hother : a = (((residues (d.modulus : ℕ) A).card : ℝ) - 1 + y) / (d.modulus : ℕ)) :
    d.left_length = y ∧
      ∀ h : ℕ+, (d.modulus : ℕ) ∣ (h : ℕ) → ∀ r : ZMod (h : ℕ),
        actualWindowProfile U hU q h A start r =
          if naturalCyclicProjection h d.modulus r =
              finiteQuotient U d.residue d.left_anchor +
                finiteValue U (fun n => (start n : ZMod (d.modulus : ℕ)))
            then y
          else if naturalCyclicProjection h d.modulus r ∈ residues (d.modulus : ℕ) A
            then 1 else 0 := by
  let m := d.modulus
  let X := ((finiteQuotient U d.residue) '' W).toFinite.toFinset
  let z := finiteValue U (fun n => (start n : ZMod (m : ℕ)))
  let S := X.image (fun r => r + z)
  have hX : (finiteQuotient U d.residue) '' W = (X : Set _) := by ext r; simp [X]
  have hScard : S.card = X.card :=
    Finset.card_image_of_injective X (fun _ _ heq => add_right_cancel heq)
  have hprofile (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) (r : ZMod (h : ℕ)) :=
    loeb_physical_bohr_left_profile U hU q W P p d hperiod A start hmodel X hX h (hdiv h) hmh r
  have hid : naturalCyclicProjection m m = AddMonoidHom.id (ZMod (m : ℕ)) := by
    ext r
    rw [naturalCyclicProjection_val m m dvd_rfl, ZMod.natCast_zmod_val]
    rfl
  have hSsub : S ⊆ residues (m : ℕ) A := by
    intro r hr
    have hp := hprofile m dvd_rfl r
    change actualWindowProfile U hU q m A start r =
      (if naturalCyclicProjection m m r = finiteQuotient U d.residue d.left_anchor + z then d.left_length
        else if naturalCyclicProjection m m r ∈ S then 1 else 0) at hp
    rw [hid] at hp
    simp only [AddMonoidHom.id_apply] at hp
    have hpos : 0 < actualWindowProfile U hU q m A start r := by
      rw [hp]
      split_ifs
      · exact d.left_positive
      · norm_num
    by_contra hn
    exact hpos.ne' (actual_window_profile_zero_outside_residues U hU q m (hdiv m) A start r hn)
  have ha : a = ((S.card : ℝ) - 1 + d.left_length) / (m : ℕ) := by
    have hmW := (congrArg ENNReal.toReal (measure_congr hmodel)).trans hmass
    rw [hScard]
    exact hmW.symm.trans (loeb_quasiBohr_right_mass U hU q P W p.swap d.swap hperiod (hdiv m) X hX)
  have heq : (S.card : ℝ) - 1 + d.left_length = ((residues (m : ℕ) A).card : ℝ) - 1 + y := by
    have hquot := ha.symm.trans hother
    exact (div_left_inj' (by exact_mod_cast m.ne_zero : ((m : ℕ) : ℝ) ≠ 0)).mp hquot
  obtain ⟨hS, hlength⟩ := FiniteProfiles.support_eq_of_partial_mass S (residues (m : ℕ) A) hSsub
    d.left_length y d.left_positive (by linarith [d.length_sum_lt_one, d.right_positive]) hy hy1 heq
  refine ⟨hlength, ?_⟩
  intro h hmh r
  have hp := hprofile h hmh r
  change actualWindowProfile U hU q h A start r =
    (if naturalCyclicProjection h m r = finiteQuotient U d.residue d.left_anchor + z then d.left_length
      else if naturalCyclicProjection h m r ∈ S then 1 else 0) at hp
  simpa only [hlength, hS] using hp

end Erdos335.Loeb

end
