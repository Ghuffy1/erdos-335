import Erdos335.LoebMixedSumDecomposition
import Erdos335.LoebDysonMixedMass
import Erdos335.DysonSumPartition

/-!
# The mixed-coset output in the strict Dyson argument

When both exclusive parts contribute inside the transformed sum, the
original sum has a quasi-periodic decomposition at the transformed
stabilizer. This is the output-set conclusion of Griesmer's Lemma 5.20,
Case 3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance dysonMixedOutputLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_dyson_mixed_case_quasiPeriodic_output
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hIpos : 0 < loebMeasure U hU (A ∩ B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU ((A ∪ B) + (A ∩ B)) <
      loebMeasure U hU (A ∪ B) + loebMeasure U hU (A ∩ B))
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) = A + B)
    (hleft : (A \ (B + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) ((A ∪ B) + (A ∩ B)) : Set _))) + B ⊆
        (A ∪ B) + (A ∩ B))
    (hright : A + (B \ (A + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) ((A ∪ B) + (A ∩ B)) : Set _))) ⊆
        (A ∪ B) + (A ∩ B)) :
    let H := AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      ((A ∪ B) + (A ∩ B))
    ∃ p : QuasiPeriodicDecomposition (loebMeasure U hU) H (A + B),
      p.background = (A ∪ B) + (A ∩ B) ∧ p.active = (A + B) \ ((A ∪ B) + (A ∩ B)) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let T := (A ∪ B) + (A ∩ B)
  let H := AddAction.stabilizer G T
  let P := dysonMixedPart H A B
  let Q := dysonMixedPart H B A
  have hUpos : 0 < μ (A ∪ B) := hIpos.trans_le (measure_mono (inter_subset_left.trans subset_union_left))
  obtain ⟨hTm, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q (A ∪ B) (A ∩ B)
    (hAm.union hBm) (hAm.inter hBm) hUpos hIpos hsmall
  have hperiod : T + (H : Set G) = T := by
    apply subset_antisymm
    · rintro x ⟨t, ht, k, hk, rfl⟩
      have hkT : k +ᵥ T = T := hk
      have hmem : k + t ∈ T := by rw [← hkT]; exact ⟨t, ht, rfl⟩
      simpa only [add_comm t k] using hmem
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hAsatm : MeasurableSet (A + (H : Set G)) :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos A
  have hBsatm : MeasurableSet (B + (H : Set G)) :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos B
  have hIsatm : MeasurableSet ((A ∩ B) + (H : Set G)) :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos (A ∩ B)
  have hPm : MeasurableSet P := (hAm.inter hBsatm).diff hIsatm
  have hQm : MeasurableSet Q := by
    simpa only [P, Q, dysonMixedPart, inter_comm B A] using (hBm.inter hAsatm).diff hIsatm
  have hsplit : A + B = T ∪ (P + Q) :=
    dyson_sum_eq_periodic_union_mixed H A B hperiod hleft hright
  have hstrict : μ T < μ (A + B) := by
    have h := hsmall
    rw [internalInnerMeasure_eq U hU T hTm, measure_union_add_inter A hBm, ← hfull] at h
    exact h
  have hbound : ∀ a ∈ P, μ (A + B) ≤ μ T +
      (μ (P ∩ (a +ᵥ (H : Set G))) + μ (Q ∩ (a +ᵥ (H : Set G)))) := by
    intro a ha
    rw [hfull]
    exact loeb_dyson_mixed_coset_bound U hU q A B hAm hBm hIpos hsmall a ha
  exact loeb_mixed_sum_quasiPeriodic_decomposition U hU q H hHm hHpos P Q (A + B) T
    hPm hQm hSm hTm hsplit hperiod (dysonMixedPart_saturation_eq H A B)
    hstrict hbound hnotperiod

end Erdos335.Loeb

end
