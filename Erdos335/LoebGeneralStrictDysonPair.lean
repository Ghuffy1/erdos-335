import Erdos335.LoebStrictDysonPair
import Erdos335.LoebPairTranslation

/-!
# The strict Dyson pair theorem at an arbitrary parameter
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance generalStrictDysonPairLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_general_strict_dyson_quasiPeriodic_pair
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (e : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hIpos : 0 < loebMeasure U hU (dysonGroupRight A B e))
    (hCpos : 0 < loebMeasure U hU (A + B)ᶜ)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (dysonGroupLeft A B e + dysonGroupRight A B e) <
      loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) →
      ¬ ∀ t ∈ K, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let C := e +ᵥ B
  have hCm : MeasurableSet C := measurable_loeb_translate U hU B hBm e
  have hCmass : μ C = μ B := loebMeasure_image_add_left U hU e B
  have hsum : A + C = e +ᵥ (A + B) := add_vadd_set_eq e A B
  have hACm : MeasurableSet (A + C) := hsum ▸ measurable_loeb_translate U hU (A + B) hSm e
  have hI : 0 < μ (A ∩ C) := by
    change 0 < μ (A ∩ (e +ᵥ B))
    rw [← dysonGroup_translate_right, show μ (e +ᵥ dysonGroupRight A B e) =
      μ (dysonGroupRight A B e) from loebMeasure_image_add_left U hU e _]
    exact hIpos
  have htotal : μ (A ∪ C) + μ (A ∩ C) = μ A + μ B := by
    rw [measure_union_add_inter A hCm, hCmass]
  have htransform : (A ∪ C) + (A ∩ C) =
      e +ᵥ (dysonGroupLeft A B e + dysonGroupRight A B e) := by
    change (A ∪ (e +ᵥ B)) + (A ∩ (e +ᵥ B)) = _
    rw [← dysonGroup_translate_right, add_vadd_set_eq]
    rfl
  have hsmall' : internalInnerMeasure U hU ((A ∪ C) + (A ∩ C)) < μ (A ∪ C) + μ (A ∩ C) := by
    rw [htotal, htransform, internalInnerMeasure_vadd]
    exact hsmall
  have hfull' : μ (A + C) = μ A + μ C := by
    rw [hsum, show μ (e +ᵥ (A + B)) = μ (A + B) from loebMeasure_image_add_left U hU e _, hCmass]
    exact hfull
  have hCpos' : 0 < μ (A + C)ᶜ := by
    rw [hsum, ← vadd_set_compl,
      show μ (e +ᵥ (A + B)ᶜ) = μ (A + B)ᶜ from loebMeasure_image_add_left U hU e _]
    exact hCpos
  have hnoAE' : ∀ K : AddSubgroup G, MeasurableSet (K : Set G) → 0 < μ (K : Set G) →
      ¬ ∀ t ∈ K, t +ᵥ (A + C) =ᵐ[μ] A + C := by
    intro K hKm hKpos hp
    apply hnoAE K hKm hKpos
    intro t ht
    have h := loeb_vadd_congr_ae U hU (t +ᵥ (A + C)) (A + C) (-e) (hp t ht)
    have hleft : (-e) +ᵥ (t +ᵥ (e +ᵥ (A + B))) = t +ᵥ (A + B) := by
      rw [vadd_vadd, vadd_vadd]
      have hcoeff : (-e + t) + e = t := by abel
      rw [hcoeff]
    simpa only [hsum, hleft, neg_vadd_vadd] using h
  obtain ⟨p⟩ := loeb_strict_dyson_quasiPeriodic_pair U hU q A C hAm hCm hACm hI hCpos' hfull'
    hsmall' (loeb_irreducible_translate_right U hU A B hirr e)
    (loeb_nonextendible_translate_right U hU A B hne e) hnoAE'
  have hreturn : Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      A ((-e) +ᵥ (e +ᵥ B))) := ⟨p.loebTranslateRight U hU (-e)⟩
  simpa only [neg_vadd_vadd] using hreturn

end Erdos335.Loeb

end
