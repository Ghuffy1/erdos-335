import Erdos335.LoebFiniteTestsPeriodicity
import Erdos335.LoebPeriodicMeasurable

/-!
# Exact periodicity in the measurable strict-deficit case

Internal inner approximation and finite augmentation extend the
periodicity conclusion of finite Kneser to arbitrary Loeb-measurable
summands in a cyclic ultraproduct.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem loeb_measurable_subcritical_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hA : MeasurableSet[loebMeasurableSpace U] A)
    (hB : MeasurableSet[loebMeasurableSpace U] B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (A + B) < loebMeasure U hU A + loebMeasure U hU B) :
    ∃ h : ℕ+,
      MeasurableSet[loebMeasurableSpace U]
        (naturalCyclicKernel U q h : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure U hU (naturalCyclicKernel U q h :
        Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      A + B + (naturalCyclicKernel U q h : Set _) = A + B := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  letI : MeasurableSpace G := loebMeasurableSpace U
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let a := (μ A).toReal
  let b := (μ B).toReal
  let c := (internalInnerMeasure U hU (A + B)).toReal
  have ha : 0 < a := ENNReal.toReal_pos hApos.ne' (measure_ne_top μ A)
  have hb : 0 < b := ENNReal.toReal_pos hBpos.ne' (measure_ne_top μ B)
  have hinnerfin : internalInnerMeasure U hU (A + B) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top μ _) (internalInnerMeasure_le U hU (A + B))
  have hc : c < a + b := by
    have hr := (ENNReal.toReal_lt_toReal hinnerfin (by finiteness)).mpr hsmall
    change c < (μ A + μ B).toReal at hr
    rw [ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ B)] at hr
    exact hr
  let ε := min a (min b (a + b - c)) / 4
  have heps : 0 < ε := by dsimp [ε]; positivity
  have hepsA : ε < a := by
    have he := min_le_left a (min b (a + b - c))
    dsimp [ε]
    linarith
  have hepsB : ε < b := by
    have he := (min_le_right a (min b (a + b - c))).trans (min_le_left b (a + b - c))
    dsimp [ε]
    linarith
  have hepsGap : 2 * ε < a + b - c := by
    have he := (min_le_right a (min b (a + b - c))).trans (min_le_right b (a + b - c))
    dsimp [ε]
    linarith
  have hrA : ENNReal.ofReal (a - ε) < μ A := by
    apply (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top μ A)).mp
    rw [ENNReal.toReal_ofReal (by linarith)]
    change a - ε < a
    linarith
  have hrB : ENNReal.ofReal (b - ε) < μ B := by
    apply (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top μ B)).mp
    rw [ENNReal.toReal_ofReal (by linarith)]
    change b - ε < b
    linarith
  obtain ⟨A₀, hA₀, hA₀gt⟩ := exists_internal_subset_measure_gt U hU A hA _ hrA
  obtain ⟨B₀, hB₀, hB₀gt⟩ := exists_internal_subset_measure_gt U hU B hB _ hrB
  have hA₀pos : 0 < μ (internalSet U A₀) :=
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < a - ε)).trans hA₀gt
  have hB₀pos : 0 < μ (internalSet U B₀) :=
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < b - ε)).trans hB₀gt
  have hA₀real : a - ε < (μ (internalSet U A₀)).toReal := by
    have hr := (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top μ _)).mpr hA₀gt
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ a - ε)] using hr
  have hB₀real : b - ε < (μ (internalSet U B₀)).toReal := by
    have hr := (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top μ _)).mpr hB₀gt
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ b - ε)] using hr
  apply exists_natural_period_of_internal_lower_bounds U hU q A B A₀ B₀ hA₀ hB₀
    (nonempty_of_measure_ne_zero hA₀pos.ne') (nonempty_of_measure_ne_zero hB₀pos.ne')
  change c < (μ (internalSet U A₀)).toReal + (μ (internalSet U B₀)).toReal
  linarith

theorem loeb_measurable_subcritical_sum_internal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hA : MeasurableSet[loebMeasurableSpace U] A)
    (hB : MeasurableSet[loebMeasurableSpace U] B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (A + B) < loebMeasure U hU A + loebMeasure U hU B) :
    ∃ C : ∀ n, Set (ZMod (q n : ℕ)), internalSet U C = A + B := by
  obtain ⟨h, _, _, hperiod⟩ := loeb_measurable_subcritical_period U hU q A B hA hB hApos hBpos hsmall
  exact exists_internalSet_of_natural_kernel_period U q h (A + B) hperiod

end Erdos335.Loeb

end
