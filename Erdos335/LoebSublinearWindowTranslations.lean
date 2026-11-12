import Erdos335.LoebFixedShiftWindow

/-!
# Translating actual windows by a sublinear sequence of integers

These lemmas retain actual membership of the translating integers. They
allow the integers to grow while their ratio to the window length tends to zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal symmDiff

noncomputable section

namespace Erdos335.Loeb

local instance sublinearWindowLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_finset_ae_eq_of_ultrafilter_discrepancy
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : ∀ n, Finset (ZMod (q n : ℕ)))
    (hsmall : Tendsto (fun n => ((((A n \ B n) ∪ (B n \ A n)).card : ℝ) / (q n : ℕ)))
      (U : Filter ℕ) (𝓝 0)) :
    internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))) =ᵐ[loebMeasure U hU]
      internalSet U (fun n => (B n : Set (ZMod (q n : ℕ)))) := by
  letI : IsProbabilityMeasure (loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU) :=
    isProbabilityMeasure_loebMeasure U hU
  have hzreal := tendsto_nhds_unique
    (loeb_finset_measure_tendsto U hU q (fun n => (A n \ B n) ∪ (B n \ A n))) hsmall
  have hz : loebMeasure U hU (internalSet U
      (fun n => (((A n \ B n) ∪ (B n \ A n) : Finset (ZMod (q n : ℕ))) :
        Set (ZMod (q n : ℕ))))) = 0 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.zero_ne_top).mp
    simpa only [ENNReal.toReal_zero] using hzreal
  simp only [Finset.coe_union, Finset.coe_sdiff, internalSet_union, internalSet_sdiff] at hz
  apply measure_symmDiff_eq_zero_iff.mp
  simpa only [Set.symmDiff_def] using hz

theorem loeb_sublinear_shift_window_eq
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ℕ) (start u : ℕ → ℕ)
    (hsmall : Tendsto (fun n => (u n : ℝ) / (q n : ℕ)) (U : Filter ℕ) (𝓝 0)) :
    productProjection (U : Filter ℕ) (fun n => (u n : ZMod (q n : ℕ))) +ᵥ
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU]
          internalSet U (fun n =>
            (cyclicWindow (shift A (u n)) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  classical
  have huq : ∀ᶠ n in U, u n < (q n : ℕ) := by
    filter_upwards [hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
    have hqpos : (0 : ℝ) < (q n : ℕ) := by exact_mod_cast (q n).pos
    have hu : (u n : ℝ) < (q n : ℕ) := (div_lt_one hqpos).mp hn
    exact_mod_cast hu
  have hdiff : Tendsto (fun n =>
      ((((cyclicWindow (shift A (u n)) (start n) (q n : ℕ) \
          (cyclicWindow A (start n) (q n : ℕ) + {(u n : ZMod (q n : ℕ))})) ∪
        ((cyclicWindow A (start n) (q n : ℕ) + {(u n : ZMod (q n : ℕ))}) \
          cyclicWindow (shift A (u n)) (start n) (q n : ℕ))).card : ℝ) / (q n : ℕ)))
      (U : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hsmall
    filter_upwards [huq] with n hn
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast fixed_shift_window_discrepancy_le A (start n) (q n : ℕ) (u n) hn)
      (by positivity)
  have heq := loeb_finset_ae_eq_of_ultrafilter_discrepancy U hU q
    (fun n => cyclicWindow (shift A (u n)) (start n) (q n : ℕ))
    (fun n => cyclicWindow A (start n) (q n : ℕ) + {(u n : ZMod (q n : ℕ))}) hdiff
  simp only [Finset.coe_add, Finset.coe_singleton, internalSet_add, internalSet_singleton] at heq
  rw [add_comm, Set.singleton_add] at heq
  exact heq.symm

theorem actual_sublinear_translate_subset_sum_window
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ℕ) (start u : ℕ → ℕ)
    (hu : ∀ᶠ n in U, u n ∈ A)
    (hsmall : Tendsto (fun n => (u n : ℝ) / (q n : ℕ)) (U : Filter ℕ) (𝓝 0)) :
    productProjection (U : Filter ℕ) (fun n => (u n : ZMod (q n : ℕ))) +ᵥ
      internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        ≤ᵐ[loebMeasure U hU]
          internalSet U (fun n =>
            (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  classical
  have heq := loeb_sublinear_shift_window_eq U hU q B start u hsmall
  have hsub : internalSet U (fun n =>
      (cyclicWindow (shift B (u n)) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ⊆
      internalSet U (fun n =>
        (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
    apply (internalSet_subset_iff U _ _).mpr
    filter_upwards [hu] with n hn x hx
    obtain ⟨b, hb, hbx⟩ := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨u n, hn, b, hb, (add_comm _ _).trans hbx⟩
  exact heq.le.trans hsub.eventuallySubset

end Erdos335.Loeb

end
