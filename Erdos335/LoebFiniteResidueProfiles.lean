import Erdos335.FiniteFiberMeasures
import Erdos335.NaturalCyclicProjection
import Erdos335.LoebTranslation

/-!
# Normalized finite residue profiles of Loeb models
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped BigOperators ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance finiteResidueProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

def loebResidueProfile (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (h : ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (r : ZMod (h : ℕ)) : ℝ :=
  (h : ℕ) * (loebMeasure U hU (S ∩
    (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r})).toReal

theorem loebResidueProfile_nonneg (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (h : ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (r : ZMod (h : ℕ)) :
    0 ≤ loebResidueProfile U hU q h S r := by
  unfold loebResidueProfile
  positivity

theorem loebResidueProfile_le_one (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h S r ≤ 1 := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  have hfiber : μ (φ ⁻¹' {r}) = (1 : ℝ≥0∞) / (h : ℕ) := by
    simpa only [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] using
      loebMeasure_naturalCyclicProjection_preimage U hU q h hd {r}
  have hle := ENNReal.toReal_mono (measure_ne_top μ (φ ⁻¹' {r}))
    (measure_mono (show S ∩ φ ⁻¹' {r} ⊆ φ ⁻¹' {r} from inter_subset_right))
  rw [hfiber, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast] at hle
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  calc
    loebResidueProfile U hU q h S r ≤ ((h : ℕ) : ℝ) * ((1 : ℝ) / (h : ℕ)) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 := by field_simp

theorem sum_loebResidueProfile (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (h : ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) :
    (∑ r, loebResidueProfile U hU q h S r) = (h : ℕ) * (loebMeasure U hU S).toReal := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  unfold loebResidueProfile
  rw [← Finset.mul_sum]
  congr 1
  apply sum_real_measure_inter_fibers μ S
  intro r
  rw [finiteQuotient_preimage_internal]
  exact measurable_internalSet U _

theorem loebResidueProfile_translate_le (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (h : ℕ+)
    (D C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hcontain : t +ᵥ D ≤ᵐ[loebMeasure U hU] C) (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h D r ≤ loebResidueProfile U hU q h C
      (r + finiteQuotient U (fun n => naturalCyclicProjection (q n) h) t) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  have heq : (fun x => t + x) '' (D ∩ φ ⁻¹' {r}) = (t +ᵥ D) ∩ φ ⁻¹' {r + φ t} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hφx⟩, rfl⟩
      change φ x = r at hφx
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      change φ (t + x) = r + φ t
      rw [map_add, hφx, add_comm]
    · rintro ⟨⟨x, hx, hxy⟩, hφy⟩
      refine ⟨x, ⟨hx, ?_⟩, hxy⟩
      change φ x = r
      change φ y = r + φ t at hφy
      change t + x = y at hxy
      rw [← hxy, map_add, add_comm (φ t)] at hφy
      exact add_right_cancel hφy
  have hsub : (t +ᵥ D) ∩ φ ⁻¹' {r + φ t} ≤ᵐ[μ] C ∩ φ ⁻¹' {r + φ t} := by
    filter_upwards [hcontain] with x hx
    exact fun h => ⟨hx h.1, h.2⟩
  have hle := measure_mono_ae hsub
  rw [← heq, loebMeasure_image_add_left] at hle
  unfold loebResidueProfile
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top μ _) hle) (by positivity)

end Erdos335.Loeb

end
