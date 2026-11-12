import Erdos335.WindowResidueRefinement
import Erdos335.LoebPeriodicWindowInputs

/-!
# Output baselines forced by one periodic actual input window
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance windowBaselinesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_periodic_input_baseline
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (T : Finset (ZMod (h : ℕ)))
    (hT : ∀ r, actualWindowProfile U hU q h B start r = if r ∈ T then (1 : ℝ) else 0) :
    ∀ r ∈ residues (h : ℕ) A + T, actualWindowProfile U hU q h (A + B) start r = 1 := by
  intro r hr
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hr
  obtain ⟨n, hn, hnu⟩ := mem_residues.mp hu
  have hle := actual_window_profile_translate_le U hU q hq h hd B A start n hn v
  change actualWindowProfile U hU q h B start v ≤
    actualWindowProfile U hU q h (B + A) start (v + (n : ZMod (h : ℕ))) at hle
  rw [hT, if_pos hv] at hle
  have hl : (1 : ℝ) ≤ actualWindowProfile U hU q h (A + B) start (u + v) := by
    simpa only [hnu, add_comm B A, add_comm v u] using hle
  exact le_antisymm (loebResidueProfile_le_one U hU q h hd _ _) hl

theorem actual_periodic_input_baseline_mass_le
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (T : Finset (ZMod (h : ℕ)))
    (hT : ∀ r, actualWindowProfile U hU q h B start r = if r ∈ T then (1 : ℝ) else 0)
    (s : ℝ) (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = s) :
    ((residues (h : ℕ) A + T).card : ℝ) / (h : ℕ) ≤ s := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hsub := actual_window_full_mask_subset U hU q h hd (A + B) start _
    (actual_periodic_input_baseline U hU q hq h hd A B start T hT)
  have hle := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  rw [loebMeasure_windowResidueMap_preimage U hU q h hd,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hmC] at hle
  exact hle

theorem saturated_periodic_input_baseline
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (T : Finset (ZMod (h : ℕ)))
    (hT : ∀ r, actualWindowProfile U hU q h B start r = if r ∈ T then (1 : ℝ) else 0)
    (s : ℝ) (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = s)
    (heq : ((residues (h : ℕ) A + T).card : ℝ) / (h : ℕ) = s) :
    internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU] windowResidueMap U q h start ⁻¹'
        ((residues (h : ℕ) A + T : Finset (ZMod (h : ℕ))) : Set (ZMod (h : ℕ))) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let C : Set G := internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  let P : Set G := windowResidueMap U q h start ⁻¹'
    ((residues (h : ℕ) A + T : Finset (ZMod (h : ℕ))) : Set (ZMod (h : ℕ)))
  have hPm : MeasurableSet P := by
    dsimp only [P]
    rw [windowResidueMap_preimage, finiteQuotient_preimage_internal]
    exact measurable_internalSet U _
  have hmass : μ C = μ P := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp
    dsimp only [P, C, μ]
    rw [hmC, loebMeasure_windowResidueMap_preimage U hU q h hd,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, heq]
  have hsub := actual_window_full_mask_subset U hU q h hd (A + B) start _
    (actual_periodic_input_baseline U hU q hq h hd A B start T hT)
  exact (ae_eq_of_ae_subset_of_measure_ge hsub hmass.le hPm.nullMeasurableSet (measure_ne_top μ C)).symm

end Erdos335.Loeb

end
