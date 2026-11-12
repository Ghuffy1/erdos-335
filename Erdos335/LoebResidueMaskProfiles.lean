import Erdos335.FiniteFiberProfiles
import Erdos335.LoebWindowProfiles

/-!
# Residue masks from finite Loeb profiles
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance residueMaskProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_ae_eq_residue_mask_of_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hS : MeasurableSet S)
    (R : Finset (ZMod (h : ℕ)))
    (hprofile : ∀ r, (loebMeasure U hU (S ∩
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r})).toReal =
      if r ∈ R then (1 : ℝ) / (h : ℕ) else 0) :
    S =ᵐ[loebMeasure U hU]
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  apply ae_eq_finite_preimage_of_fiber_measures μ _ S hS R
  intro r
  have hfiber : μ ((finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r}) =
      (1 : ℝ≥0∞) / (h : ℕ) := by
    simpa only [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] using
      loebMeasure_naturalCyclicProjection_preimage U hU q h hd {r}
  by_cases hr : r ∈ R
  · rw [if_pos hr, hfiber]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (by finiteness)).mp
    simpa only [if_pos hr, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast] using hprofile r
  · rw [if_neg hr]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.zero_ne_top).mp
    simpa only [if_neg hr, ENNReal.toReal_zero] using hprofile r

end Erdos335.Loeb

end
