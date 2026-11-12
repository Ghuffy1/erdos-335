import Erdos335.LoebEmbeddingMeasurability
import Erdos335.LoebEmbeddingInner
import Erdos335.LoebIrreducibleCore
import Erdos335.LoebNonextendible

/-!
# Pair hypotheses in positive internal subgroup coordinates
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X Y : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
variable [∀ n, Finite (X n)] [∀ n, Finite (Y n)]

local instance embeddingPairSourceSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance embeddingPairTargetSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product Y) := loebMeasurableSpace U

theorem loeb_irreducible_of_internal_embedding
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (p : ∀ n, X n →+ Y n) (hp : ∀ n, Function.Injective (p n))
    (hpos : 0 < loebMeasure U hU (Set.range (productMapHom (U : Filter ℕ) p)))
    (A B : Set ((U : Filter ℕ).Product X))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (productMapHom (U : Filter ℕ) p '' A) (productMapHom (U : Filter ℕ) p '' B)) :
    MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B := by
  let e := productMapHom (U : Filter ℕ) p
  let c := loebMeasure U hU (Set.range e)
  have hc : c ≠ ∞ := ne_of_lt (calc
    c ≤ loebMeasure (X := Y) U hU univ := measure_mono (subset_univ _)
    _ = 1 := loebMeasure_univ U hU
    _ < ∞ := by simp)
  have hm (S : Set ((U : Filter ℕ).Product X)) :
      loebMeasure U hU (e '' S) = c * loebMeasure U hU S :=
    loebMeasure_image_injection U hU (fun n => p n) hp hpos S
  have hi (S : Set ((U : Filter ℕ).Product X)) :
      internalInnerMeasure U hU (e '' S) = c * internalInnerMeasure U hU S :=
    internalInnerMeasure_image_injection U hU (fun n => p n) hp S
  have he := measurableEmbedding_positive_internal_injection U hU (fun n => p n) hp hpos
  intro P Q hPm hQm hPA hQB hPmass hQmass
  have h := hirr (e '' P) (e '' Q) (he.measurableSet_image.mpr hPm)
    (he.measurableSet_image.mpr hQm) (image_mono hPA) (image_mono hQB)
    (by rw [hm, hm, hPmass]) (by rw [hm, hm, hQmass])
  rw [← Set.image_add e, ← Set.image_add e, hi, hi] at h
  exact (ENNReal.mul_right_inj hpos.ne' hc).mp h

theorem loeb_nonextendible_of_internal_embedding
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (p : ∀ n, X n →+ Y n) (hp : ∀ n, Function.Injective (p n))
    (hpos : 0 < loebMeasure U hU (Set.range (productMapHom (U : Filter ℕ) p)))
    (A B : Set ((U : Filter ℕ).Product X))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU)
      (productMapHom (U : Filter ℕ) p '' A) (productMapHom (U : Filter ℕ) p '' B)) :
    MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B := by
  let e := productMapHom (U : Filter ℕ) p
  let c := loebMeasure U hU (Set.range e)
  have hc : c ≠ ∞ := ne_of_lt (calc
    c ≤ loebMeasure (X := Y) U hU univ := measure_mono (subset_univ _)
    _ = 1 := loebMeasure_univ U hU
    _ < ∞ := by simp)
  have hm (S : Set ((U : Filter ℕ).Product X)) :
      loebMeasure U hU (e '' S) = c * loebMeasure U hU S :=
    loebMeasure_image_injection U hU (fun n => p n) hp hpos S
  have hi (S : Set ((U : Filter ℕ).Product X)) :
      internalInnerMeasure U hU (e '' S) = c * internalInnerMeasure U hU S :=
    internalInnerMeasure_image_injection U hU (fun n => p n) hp S
  have he := measurableEmbedding_positive_internal_injection U hU (fun n => p n) hp hpos
  intro P Q hPm hQm hAP hBQ hsame
  have hsame' : internalInnerMeasure U hU ((e '' P) + (e '' Q)) =
      internalInnerMeasure U hU ((e '' A) + (e '' B)) := by
    rw [← Set.image_add e, ← Set.image_add e, hi, hi, hsame]
  have h := hne (e '' P) (e '' Q) (he.measurableSet_image.mpr hPm)
    (he.measurableSet_image.mpr hQm) (image_mono hAP) (image_mono hBQ) hsame'
  rw [hm, hm, hm, hm, ← mul_add, ← mul_add] at h
  exact (ENNReal.mul_le_mul_iff_right hpos.ne' hc).mp h

end Erdos335.Loeb

end
