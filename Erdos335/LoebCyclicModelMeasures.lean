import Erdos335.LoebAverages
import Erdos335.LoebGroup

/-!
# Measures of the finite cyclic models
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators ENNReal Pointwise

namespace Erdos335.Loeb

theorem loeb_finset_measure_tendsto (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (A : ∀ n, Finset (ZMod (q n : ℕ))) :
    Tendsto (fun n => ((A n).card : ℝ) / (q n : ℕ)) (U : Filter ℕ)
      (𝓝 ((loebMeasure U hU (internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))))).toReal)) := by
  rw [loebMeasure_internal]
  have hfinite : ultraCount U (fun n => (A n : Set (ZMod (q n : ℕ)))) ≠ ∞ :=
    ne_of_lt ((ultraCount_le_one U _).trans_lt ENNReal.one_lt_top)
  have h := (ENNReal.tendsto_toReal hfinite).comp (tendsto_ultraCount U (fun n => (A n : Set (ZMod (q n : ℕ)))))
  simpa only [Function.comp_def, countingRatio_toReal, Set.ncard_coe_finset,
    Nat.card_eq_fintype_card, ZMod.card] using h

theorem loeb_finset_measure_eq (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (A : ∀ n, Finset (ZMod (q n : ℕ))) (a : ℝ)
    (hA : Tendsto (fun n => ((A n).card : ℝ) / (q n : ℕ)) atTop (𝓝 a)) :
    (loebMeasure U hU (internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))))).toReal = a :=
  tendsto_nhds_unique (loeb_finset_measure_tendsto U hU q A) (hA.mono_left hU)

theorem finset_sum_card_le_container (G : Type*) [Add G] [DecidableEq G]
    (A B C : Finset G) : (A + B).card ≤ C.card + ((A + B) \ C).card := by
  classical
  have hsub : A + B ⊆ C ∪ ((A + B) \ C) := by
    intro x hx
    by_cases hc : x ∈ C
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hc⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem loeb_cyclic_sum_measure_le (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (A B C : ∀ n, Finset (ZMod (q n : ℕ))) (c : ℝ)
    (hC : Tendsto (fun n => ((C n).card : ℝ) / (q n : ℕ)) atTop (𝓝 c))
    (hspill : Tendsto (fun n => (((A n + B n) \ C n).card : ℝ) / (q n : ℕ)) atTop (𝓝 0)) :
    (loebMeasure U hU
      (internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))) +
        internalSet U (fun n => (B n : Set (ZMod (q n : ℕ)))))).toReal ≤ c := by
  have hleft := loeb_finset_measure_tendsto U hU q (fun n => A n + B n)
  have hright : Tendsto (fun n => ((C n).card : ℝ) / (q n : ℕ) +
      (((A n + B n) \ C n).card : ℝ) / (q n : ℕ)) (U : Filter ℕ) (𝓝 c) := by
    simpa only [add_zero] using (hC.add hspill).mono_left hU
  have hbound := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun n => by
    dsimp only
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast finset_sum_card_le_container _ (A n) (B n) (C n))
  simpa only [Finset.coe_add, internalSet_add] using hbound

end Erdos335.Loeb
