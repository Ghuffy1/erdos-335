import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Sigma-compact representatives of measurable sets

Inner regularity supplies countably many compact subsets whose union loses
zero measure. Their sum is again sigma-compact and therefore Borel.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

namespace Erdos335.Loeb

theorem exists_full_measure_sigmaCompact_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (A : Set X) (hA : MeasurableSet A) :
    ∃ C : Set X, C ⊆ A ∧ IsSigmaCompact C ∧ MeasurableSet C ∧ μ C = μ A := by
  choose K hKA hKcompact hKerror using fun n : ℕ =>
    hA.exists_isCompact_sdiff_lt (measure_ne_top μ A)
      (show ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≠ 0 by positivity)
  let C := ⋃ n, K n
  have hCA : C ⊆ A := iUnion_subset hKA
  have hzero : μ (A \ C) = 0 := by
    apply le_antisymm _ zero_le
    apply ge_of_tendsto' (show Tendsto
      (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) from by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat)
    intro n
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion K n))).trans (hKerror n).le
  exact ⟨C, hCA, isSigmaCompact_iUnion_of_isCompact K hKcompact,
    MeasurableSet.iUnion (fun n => (hKcompact n).measurableSet),
    measure_eq_measure_of_null_sdiff hCA hzero⟩

end Erdos335.Loeb
