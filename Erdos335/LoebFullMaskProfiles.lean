import Erdos335.LoebProfileBounds

/-!
# Full quotient profiles give almost-everywhere inclusion of the mask
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance fullMaskProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_fiber_ae_subset_of_full_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hS : MeasurableSet S)
    (r : ZMod (h : ℕ)) (hfull : loebResidueProfile U hU q h S r = 1) :
    (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r} ≤ᵐ[loebMeasure U hU] S := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  let F := φ ⁻¹' {r}
  have hFm : MeasurableSet F := by
    change MeasurableSet ((finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r})
    rw [finiteQuotient_preimage_internal]
    exact measurable_internalSet U _
  have hmassF : μ F = (1 : ℝ≥0∞) / (h : ℕ) := by
    have heq := loebMeasure_naturalCyclicProjection_preimage U hU q h hd {r}
    simpa only [Finset.card_singleton, Nat.cast_one, Finset.coe_singleton] using heq
  have hmass : μ (S ∩ F) = μ F := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp
    change ((h : ℕ) : ℝ) * (μ (S ∩ F)).toReal = 1 at hfull
    rw [hmassF, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
    apply (eq_div_iff (by exact_mod_cast h.ne_zero : ((h : ℕ) : ℝ) ≠ 0)).mpr
    simpa only [mul_comm] using hfull
  have hzero : μ (F \ (S ∩ F)) = 0 := by
    rw [measure_sdiff inter_subset_right (hS.inter hFm).nullMeasurableSet (measure_ne_top μ _), hmass, tsub_self]
  have hf := ae_le_set.mpr hzero
  filter_upwards [hf] with x hx hxr
  exact (hx hxr).1

theorem loeb_mask_ae_subset_of_full_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hS : MeasurableSet S)
    (R : Finset (ZMod (h : ℕ))) (hfull : ∀ r ∈ R, loebResidueProfile U hU q h S r = 1) :
    (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) ≤ᵐ[loebMeasure U hU] S := by
  classical
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  have hf : ∀ r, ∀ᵐ x ∂loebMeasure U hU, r ∈ R → φ x = r → x ∈ S := by
    intro r
    by_cases hr : r ∈ R
    · have hsub := loeb_fiber_ae_subset_of_full_profile U hU q h hd S hS r (hfull r hr)
      filter_upwards [hsub] with x hx _ hxr
      exact hx hxr
    · exact Filter.Eventually.of_forall fun _ h => (hr h).elim
  filter_upwards [ae_all_iff.mpr hf] with x hx hmem
  exact hx (φ x) hmem rfl

end Erdos335.Loeb

end
