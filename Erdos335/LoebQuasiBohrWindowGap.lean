import Erdos335.LoebQuasiBohrFiniteProfiles
import Erdos335.LoebWindowMaskBounds
import Erdos335.ResidueCapacityMasks

/-!
# Positive residue-capacity gaps for quasi-periodic Bohr window models
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiBohrWindowGapLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem quasiPeriodicBohr_right_window_gap
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (P W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) P W)
    (b : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U b.residue).ker)
    (A : Set ℕ) (start : ℕ → ℕ)
    (hWA : W =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (a : ℝ) (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℕ+, a + δ ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
  classical
  let m := b.modulus
  let f := finiteQuotient U b.residue
  let R := (f '' W).toFinite.toFinset
  have hR : f '' W = (R : Set _) := by ext x; simp [R]
  let z₀ := finiteValue U (fun n => (start n : ZMod (m : ℕ)))
  let T := R.image (fun r => r + z₀)
  have hTcard : T.card = R.card := Finset.card_image_of_injective R (fun x y hxy => add_right_cancel hxy)
  have hmass : a = ((R.card : ℝ) - 1 + b.right_length) / (m : ℕ) := by
    have hmW := (congrArg ENNReal.toReal (measure_congr hWA)).trans hmA
    exact hmW.symm.trans (loeb_quasiBohr_right_mass U hU q P W p b hperiod (hdiv m) R hR)
  have hcapacity (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) :
      (R.card : ℝ) / (m : ℕ) ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
    rw [← hTcard]
    apply residue_capacity_ge_of_full_coarse_mask A m h hmh T
    intro r hr
    let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
    have hphase : naturalCyclicProjection h m z = z₀ := by
      have hp := windowResidueMap_refinement U q h m start (hdiv h) hmh 0
      simpa only [windowResidueMap, map_zero, zero_add, z, z₀] using hp
    obtain ⟨v, hv, hvr⟩ := Finset.mem_image.mp hr
    have hvr' : naturalCyclicProjection h m (r - z) = v := by
      rw [map_sub, hphase, ← hvr, add_sub_cancel_right]
    have hin : naturalCyclicProjection h m (r - z) ∈ (f '' W) := by
      rw [hvr', hR]
      exact hv
    have hp := loeb_quasiBohr_right_residue_profile U hU q P W p b hperiod h (hdiv h) hmh (r - z)
    have hpos : 0 < loebResidueProfile U hU q h W (r - z) := by
      by_cases hc : naturalCyclicProjection h m (r - z) = f b.right_anchor
      · rw [if_pos hc] at hp
        rw [hp]
        exact b.right_positive
      · rw [if_neg hc, if_pos hin] at hp
        rw [hp]
        norm_num
    have hwindowPos : 0 < actualWindowProfile U hU q h A start r := by
      change 0 < loebResidueProfile U hU q h _ (r - z)
      rw [← loebResidueProfile_eq_of_ae U hU q h W _ hWA]
      exact hpos
    by_contra hn
    have hz := actual_window_profile_zero_outside_residues U hU q h (hdiv h) A start r hn
    exact hwindowPos.ne' hz
  have hall (k : ℕ+) : (R.card : ℝ) / (m : ℕ) ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) := by
    have hmk : (m : ℕ) ∣ ((m * k : ℕ+) : ℕ) := ⟨k, rfl⟩
    have hkm : (k : ℕ) ∣ ((m * k : ℕ+) : ℕ) := ⟨m, Nat.mul_comm _ _⟩
    exact (hcapacity (m * k) hmk).trans (residue_capacity_mono_of_dvd A k (m * k) hkm)
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hstrict : a < (R.card : ℝ) / (m : ℕ) := by
    rw [hmass]
    apply (div_lt_div_iff_of_pos_right hmpos).mpr
    linarith [b.length_sum_lt_one, b.left_positive]
  refine ⟨(R.card : ℝ) / (m : ℕ) - a, sub_pos.mpr hstrict, ?_⟩
  intro k
  have hk := hall k
  linarith

end Erdos335.Loeb

end
