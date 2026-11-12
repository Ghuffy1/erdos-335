import Erdos335.LoebCyclicModelMeasures

/-!
# Almost-everywhere containment for the finite cyclic models
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance cyclicModelContainmentLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_finset_ae_eq_of_same_density (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (A B : ∀ n, Finset (ZMod (q n : ℕ))) (a : ℝ)
    (hsub : ∀ n, A n ⊆ B n)
    (hA : Tendsto (fun n => ((A n).card : ℝ) / (q n : ℕ)) atTop (𝓝 a))
    (hB : Tendsto (fun n => ((B n).card : ℝ) / (q n : ℕ)) atTop (𝓝 a)) :
    internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))) =ᵐ[loebMeasure U hU]
      internalSet U (fun n => (B n : Set (ZMod (q n : ℕ)))) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hAB : internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))) ⊆
      internalSet U (fun n => (B n : Set (ZMod (q n : ℕ)))) := by
    apply (internalSet_subset_iff U _ _).mpr
    exact Eventually.of_forall hsub
  have heq : μ (internalSet U (fun n => (A n : Set (ZMod (q n : ℕ))))) =
      μ (internalSet U (fun n => (B n : Set (ZMod (q n : ℕ))))) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp
    rw [loeb_finset_measure_eq U hU q A a hA, loeb_finset_measure_eq U hU q B a hB]
  refine hAB.eventuallySubset.antisymm (ae_le_set.mpr ?_)
  rw [measure_sdiff hAB (measurable_internalSet U _).nullMeasurableSet (measure_ne_top μ _), heq,
    tsub_self]

theorem loeb_cyclic_sum_ae_subset (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (A B C : ∀ n, Finset (ZMod (q n : ℕ)))
    (hspill : Tendsto (fun n => (((A n + B n) \ C n).card : ℝ) / (q n : ℕ)) atTop (𝓝 0)) :
    internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))) +
        internalSet U (fun n => (B n : Set (ZMod (q n : ℕ)))) ≤ᵐ[loebMeasure U hU]
      internalSet U (fun n => (C n : Set (ZMod (q n : ℕ)))) := by
  apply ae_le_set.mpr
  have hzero := loeb_finset_measure_eq U hU q (fun n => (A n + B n) \ C n) 0 hspill
  have hfinite : loebMeasure U hU
      (internalSet U (fun n => (((A n + B n) \ C n : Finset (ZMod (q n : ℕ))) :
        Set (ZMod (q n : ℕ))))) ≠ ∞ := by
    rw [loebMeasure_internal]
    exact ne_of_lt ((ultraCount_le_one U _).trans_lt ENNReal.one_lt_top)
  have hz := (ENNReal.toReal_eq_toReal_iff' hfinite ENNReal.zero_ne_top).mp
    (show (loebMeasure U hU (internalSet U
      (fun n => (((A n + B n) \ C n : Finset (ZMod (q n : ℕ))) : Set (ZMod (q n : ℕ)))))).toReal =
        (0 : ℝ≥0∞).toReal by simpa only [ENNReal.toReal_zero] using hzero)
  simpa only [Finset.coe_sdiff, Finset.coe_add, internalSet_sdiff, internalSet_add] using hz

theorem loeb_literal_translate_ae_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (E : ℕ → Set ℕ) (C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hsub : D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) ≤ᵐ[loebMeasure U hU] C)
    (b : ℕ) (hb : ∀ᶠ n in U, b ∈ E n) :
    productProjection (U : Filter ℕ) (fun n => (b : ZMod (q n : ℕ))) +ᵥ D ≤ᵐ[loebMeasure U hU] C := by
  have hmem : productProjection (U : Filter ℕ) (fun n => (b : ZMod (q n : ℕ))) ∈
      internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) :=
    hb.mono (fun n hn => ⟨b, hn, rfl⟩)
  have htranslate : productProjection (U : Filter ℕ) (fun n => (b : ZMod (q n : ℕ))) +ᵥ D ⊆
      D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) := by
    rintro x ⟨d, hd, rfl⟩
    exact ⟨d, hd, _, hmem, add_comm _ _⟩
  exact htranslate.eventuallySubset.trans hsub

end Erdos335.Loeb

end
