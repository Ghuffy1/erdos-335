import Erdos335.CyclicWindowFixedShift
import Erdos335.LoebCyclicModelContainment
import Erdos335.LoebWindowTranslations

/-!
# Two-sided fixed-shift agreement for actual windows
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal symmDiff

noncomputable section

namespace Erdos335.Loeb

local instance fixedShiftWindowLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_finset_ae_eq_of_discrepancy
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : ∀ n, Finset (ZMod (q n : ℕ)))
    (hsmall : Tendsto (fun n => ((((A n \ B n) ∪ (B n \ A n)).card : ℝ) / (q n : ℕ)))
      atTop (𝓝 0)) :
    internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))) =ᵐ[loebMeasure U hU]
      internalSet U (fun n => (B n : Set (ZMod (q n : ℕ)))) := by
  letI : IsProbabilityMeasure (loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU) :=
    isProbabilityMeasure_loebMeasure U hU
  have hzero := loeb_finset_measure_eq U hU q (fun n => (A n \ B n) ∪ (B n \ A n)) 0 hsmall
  have hz : loebMeasure U hU (internalSet U
      (fun n => (((A n \ B n) ∪ (B n \ A n) : Finset (ZMod (q n : ℕ))) : Set (ZMod (q n : ℕ))))) = 0 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.zero_ne_top).mp
    simpa only [ENNReal.toReal_zero] using hzero
  simp only [Finset.coe_union, Finset.coe_sdiff, internalSet_union, internalSet_sdiff] at hz
  apply measure_symmDiff_eq_zero_iff.mp
  simpa only [Set.symmDiff_def] using hz

theorem loeb_fixed_shift_window_eq
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A : Set ℕ) (start : ℕ → ℕ) (u : ℕ) :
    productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU]
          internalSet U (fun n => (cyclicWindow (shift A u) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  classical
  have hsmall : Tendsto (fun n =>
      ((((cyclicWindow (shift A u) (start n) (q n : ℕ) \
          (cyclicWindow A (start n) (q n : ℕ) + {(u : ZMod (q n : ℕ))})) ∪
        ((cyclicWindow A (start n) (q n : ℕ) + {(u : ZMod (q n : ℕ))}) \
          cyclicWindow (shift A u) (start n) (q n : ℕ))).card : ℝ) / (q n : ℕ))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
      ((tendsto_const_div_atTop_nhds_zero_nat (u : ℝ)).comp hq)
    filter_upwards [hq.eventually (eventually_gt_atTop u)] with n hn
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast fixed_shift_window_discrepancy_le A (start n) (q n : ℕ) u hn) (by positivity)
  have heq := loeb_finset_ae_eq_of_discrepancy U hU q
    (fun n => cyclicWindow (shift A u) (start n) (q n : ℕ))
    (fun n => cyclicWindow A (start n) (q n : ℕ) + {(u : ZMod (q n : ℕ))}) hsmall
  simp only [Finset.coe_add, Finset.coe_singleton, internalSet_add, internalSet_singleton] at heq
  rw [add_comm, Set.singleton_add] at heq
  exact heq.symm

end Erdos335.Loeb

end
