import Erdos335.LoebBohrPairProfiles
import Erdos335.LoebWindowMaskBounds
import Erdos335.ResidueCapacityRefinement

/-!
# A positive Bohr model gives a positive literal residue-capacity gap
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance bohrWindowGapLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem internalBohrPair_right_window_gap
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (P W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (b : InternalBohrPairData U hU q P W) (A : Set ℕ) (start : ℕ → ℕ)
    (hWA : W =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (a : ℝ) (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℕ+, a + δ ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let m := b.modulus
  have hquotient : finiteQuotient U b.residue =
      finiteQuotient U (fun n => naturalCyclicProjection (q n) m) := by
    apply finiteQuotient_eq_of_eventually_natural
    · exact b.natural_residue.mono fun n hn => hn.2
    · exact (hdiv m).mono fun n hn k => naturalCyclicProjection_natCast (q n) m hn k
  have hprofile (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) := (b.residue_profiles h (hdiv h) hmh).2
  have hWmass : (μ W).toReal = a := (congrArg ENNReal.toReal (measure_congr hWA)).trans hmA
  have hWsub : W ⊆ (finiteQuotient U b.residue) ⁻¹' {finiteQuotient U b.residue b.right_anchor} := by
    have hc := b.right_containment.trans inter_subset_left
    rwa [← addHom_fiber_eq_coset] at hc
  have hmass : a = b.right_length / (m : ℕ) := by
    have hp := hprofile m dvd_rfl (finiteQuotient U b.residue b.right_anchor)
    have hident : naturalCyclicProjection m m = AddMonoidHom.id (ZMod (m : ℕ)) := by
      ext r
      rw [naturalCyclicProjection_val m m dvd_rfl, ZMod.natCast_zmod_val]
      rfl
    rw [hident, AddMonoidHom.id_apply, if_pos rfl] at hp
    unfold loebResidueProfile at hp
    rw [← hquotient, inter_eq_self_of_subset_left hWsub, hWmass] at hp
    apply (eq_div_iff (by exact_mod_cast m.ne_zero : ((m : ℕ) : ℝ) ≠ 0)).mpr
    simpa only [mul_comm] using hp
  have hcapacity (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) :
      (1 : ℝ) / (m : ℕ) ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
    apply residue_capacity_ge_of_full_coarse_fiber A m h hmh (windowResidueMap U q m start b.right_anchor)
    intro r hr
    let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
    have hphase : naturalCyclicProjection h m z = finiteValue U (fun n => (start n : ZMod (m : ℕ))) := by
      have hp := windowResidueMap_refinement U q h m start (hdiv h) hmh 0
      simpa only [windowResidueMap, map_zero, zero_add, z] using hp
    have hcond : naturalCyclicProjection h m (r - z) = finiteQuotient U b.residue b.right_anchor := by
      change naturalCyclicProjection h m r = windowResidueMap U q m start b.right_anchor at hr
      rw [windowResidueMap, ← hquotient] at hr
      rw [map_sub, hphase, hr, add_sub_cancel_right]
    have hp := hprofile h hmh (r - z)
    rw [if_pos hcond] at hp
    have hpos : 0 < actualWindowProfile U hU q h A start r := by
      change 0 < loebResidueProfile U hU q h _ (r - z)
      rw [← loebResidueProfile_eq_of_ae U hU q h W _ hWA, hp]
      exact b.right_positive
    by_contra hn
    have hz := actual_window_profile_zero_outside_residues U hU q h (hdiv h) A start r hn
    exact hpos.ne' hz
  have hall (k : ℕ+) : (1 : ℝ) / (m : ℕ) ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) := by
    have hmk : (m : ℕ) ∣ ((m * k : ℕ+) : ℕ) := ⟨k, rfl⟩
    have hkm : (k : ℕ) ∣ ((m * k : ℕ+) : ℕ) := ⟨m, Nat.mul_comm _ _⟩
    exact (hcapacity (m * k) hmk).trans (residue_capacity_mono_of_dvd A k (m * k) hkm)
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hstrict : a < (1 : ℝ) / (m : ℕ) := by
    rw [hmass]
    exact (div_lt_div_iff_of_pos_right hmpos).mpr (by linarith [b.length_sum_lt_one, b.left_positive])
  refine ⟨(1 : ℝ) / (m : ℕ) - a, sub_pos.mpr hstrict, ?_⟩
  intro k
  have hk := hall k
  linarith

end Erdos335.Loeb

end
