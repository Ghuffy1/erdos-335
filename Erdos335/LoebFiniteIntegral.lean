import Erdos335.LoebFiniteFunctions
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Integrating finite-valued internal functions

Finite-valued functions have the expected weighted counting integral.
The corresponding finite weighted averages converge along the ultrafilter.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]
  {G : Type*} [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem integral_finiteFunction (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → G) (v : G → ℝ) :
    (∫ x, v (finiteFunction U f x) ∂loebMeasure U hU) =
      ∑ g, (ultraCount U (fun n => f n ⁻¹' {g})).toReal * v g := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let μ := loebMeasure (X := X) U hU
  let F : (U : Filter ℕ).Product X → G := finiteFunction U f
  let : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hF : Measurable F := measurable_finiteFunction U f
  have hv : Integrable v (Measure.map F μ) := Integrable.of_finite
  calc
    (∫ x, v (F x) ∂μ) = ∫ g, v g ∂Measure.map F μ :=
      (integral_map hF.aemeasurable hv.aestronglyMeasurable).symm
    _ = ∑ g, (Measure.map F μ).real {g} • v g := integral_fintype hv
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      rw [map_measureReal_apply hF (measurableSet_singleton g), measureReal_def]
      change (loebMeasure U hU (finiteFunction U f ⁻¹' {g})).toReal • v g = _
      rw [loebMeasure_finiteFunction_preimage, smul_eq_mul]

theorem tendsto_finite_weighted_averages (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, X n → G) (v : G → ℝ) :
    Tendsto (fun n => ∑ g, (countingRatio (f n ⁻¹' {g})).toReal * v g)
      (U : Filter ℕ) (𝓝 (∫ x, v (finiteFunction U f x) ∂loebMeasure U hU)) := by
  rw [integral_finiteFunction]
  apply tendsto_finsetSum
  intro g _
  have hfinite : ultraCount U (fun n => f n ⁻¹' {g}) ≠ ∞ :=
    ne_of_lt ((ultraCount_le_one U _).trans_lt ENNReal.one_lt_top)
  exact ((ENNReal.tendsto_toReal hfinite).comp (tendsto_ultraCount U _)).mul tendsto_const_nhds

end Erdos335.Loeb
