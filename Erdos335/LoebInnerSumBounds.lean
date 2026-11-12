import Erdos335.LoebCosetSums
import Erdos335.CompactDysonTransform
import Erdos335.LoebInnerAE

/-!
# Inner-measure lower bounds from individual translates
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance innerSumBoundsLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_left_measure_le_sum_inner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X)) (hAm : MeasurableSet A) (hB : B.Nonempty) :
    loebMeasure U hU A ≤ internalInnerMeasure U hU (A + B) := by
  obtain ⟨b, hb⟩ := hB
  have htransm : MeasurableSet (b +ᵥ A) := by
    rw [vadd_set_eq_neg_preimage]
    exact hAm.preimage (measurable_add_left U hU (-b))
  have hsub : b +ᵥ A ⊆ A + B := by
    rintro x ⟨a, ha, rfl⟩
    exact ⟨a, ha, b, hb, add_comm _ _⟩
  calc
    loebMeasure U hU A = loebMeasure U hU (b +ᵥ A) := (loebMeasure_image_add_left U hU b A).symm
    _ = internalInnerMeasure U hU (b +ᵥ A) := (internalInnerMeasure_eq U hU _ htransm).symm
    _ ≤ internalInnerMeasure U hU (A + B) := internalInnerMeasure_mono U hU hsub

theorem loeb_positive_of_strict_sum_deficit
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hsmall : internalInnerMeasure U hU (A + B) < loebMeasure U hU A + loebMeasure U hU B) :
    0 < loebMeasure U hU A ∧ 0 < loebMeasure U hU B := by
  have hleft := loeb_left_measure_le_sum_inner U hU A B hAm hB
  have hright := loeb_left_measure_le_sum_inner U hU B A hBm hA
  rw [add_comm B A] at hright
  constructor
  · by_contra h
    have hz : loebMeasure U hU A = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt h)
    rw [hz, zero_add] at hsmall
    exact (not_lt_of_ge hright) hsmall
  · by_contra h
    have hz : loebMeasure U hU B = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt h)
    rw [hz, add_zero] at hsmall
    exact (not_lt_of_ge hleft) hsmall

end Erdos335.Loeb

end
