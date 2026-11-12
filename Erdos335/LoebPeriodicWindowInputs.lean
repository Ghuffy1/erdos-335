import Erdos335.LoebPeriodicWindowProfiles
import Erdos335.LoebShiftedProfileMasks
import Erdos335.LoebWindowPeriodTransfer

/-!
# Periodicity of both actual inputs from a periodic output window
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance periodicWindowInputsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_window_profile_of_residue_mask
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (R : Finset (ZMod (h : ℕ)))
    (hmask : internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) =ᵐ[loebMeasure U hU]
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _)) :
    ∀ r, actualWindowProfile U hU q h A start r =
      if r ∈ R.image (fun t => t + finiteValue U (fun n => (start n : ZMod (h : ℕ)))) then (1 : ℝ) else 0 := by
  classical
  intro r
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  have hmem : r ∈ R.image (fun t => t + z) ↔ r - z ∈ R := by
    constructor
    · intro hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
      simpa only [add_sub_cancel_right] using ht
    · intro hr
      exact Finset.mem_image.mpr ⟨r - z, hr, sub_add_cancel _ _⟩
  have hp := loeb_residue_mask_profile U hU q h hd _ R hmask (r - z)
  unfold actualWindowProfile loebResidueProfile
  change ((h : ℕ) : ℝ) * (loebMeasure U hU (_ ∩ _)).toReal =
    if r ∈ R.image (fun t => t + z) then 1 else 0
  rw [hp]
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  by_cases hr : r - z ∈ R
  · rw [if_pos hr, if_pos (hmem.mpr hr)]
    field_simp
  · rw [if_neg hr, if_neg (fun h => hr (hmem.mp h)), mul_zero]

theorem periodic_output_window_forces_periodic_inputs
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun s => (q s : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (R : Finset (ZMod (h : ℕ)))
    (hmask : internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) :
      Set (ZMod (q n : ℕ)))) =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _)) :
    ∃ P Q : Finset (ZMod (h : ℕ)),
      (internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (P : Set _) ∧
      (internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (Q : Set _) := by
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  obtain ⟨P, Q, hPsub, hQsub, hcard, hP, hQ, hfill⟩ := periodic_output_window_profiles U hU q hq h hd
    A B start a b ha hb hmA hmB hmC hgap (R.image (fun r => r + z))
      (actual_window_profile_of_residue_mask U hU q h hd (A + B) start R hmask)
  refine ⟨P.image (fun r => r - z), Q.image (fun r => r - z), ?_, ?_⟩
  · exact loeb_ae_eq_shifted_mask_of_full_profile U hU q h hd _ (measurable_internalSet U _) P z hP
  · exact loeb_ae_eq_shifted_mask_of_full_profile U hU q h hd _ (measurable_internalSet U _) Q z hQ

end Erdos335.Loeb

end
