import Erdos335.LoebPairTranslation
import Erdos335.LoebZeroActiveCore
import Erdos335.LoebQuasiPeriodicLifting

/-!
# Translating both inputs of a Loeb equality pair
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance pairCenteringLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_irreducible_translate_pair
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (a b : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) (a +ᵥ A) (b +ᵥ B) := by
  have hleft := (loeb_irreducible_translate_right U hU B A hirr.swap a).swap
  exact loeb_irreducible_translate_right U hU (a +ᵥ A) B hleft b

theorem loeb_nonextendible_translate_pair
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (a b : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) (a +ᵥ A) (b +ᵥ B) := by
  have hleft := (loeb_nonextendible_translate_right U hU B A hne.swap a).swap
  exact loeb_nonextendible_translate_right U hU (a +ᵥ A) B hleft b

theorem loeb_ae_period_translate_iff
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (a t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    t +ᵥ (a +ᵥ S) =ᵐ[loebMeasure U hU] a +ᵥ S ↔ t +ᵥ S =ᵐ[loebMeasure U hU] S := by
  have hcomm : t +ᵥ (a +ᵥ S) = a +ᵥ (t +ᵥ S) := by
    rw [vadd_vadd, vadd_vadd, add_comm t a]
  rw [hcomm]
  constructor
  · intro h
    have h' := loeb_vadd_congr_ae U hU _ _ (-a) h
    simpa only [neg_vadd_vadd] using h'
  · exact fun h => loeb_vadd_congr_ae U hU _ _ a h

end Erdos335.Loeb

end
