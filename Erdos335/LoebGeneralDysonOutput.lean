import Erdos335.LoebTranslationStructure
import Erdos335.LoebDysonOutput

/-!
# The output model for an arbitrary strict Dyson transform

Translation reduces a general transform parameter to the zero-parameter
coset argument, and transports the resulting quasi-periodic output model
back to the original sum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance generalDysonOutputLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_general_strict_dyson_output_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (e : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hIpos : 0 < loebMeasure U hU (dysonGroupRight A B e))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (dysonGroupLeft A B e + dysonGroupRight A B e) <
      loebMeasure U hU A + loebMeasure U hU B)
    (hnotperiod : ¬ ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      (A + B) + (H : Set _) = A + B) :
    ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      ∃ D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
        Nonempty (QuasiPeriodicDecomposition (loebMeasure U hU) H D) ∧
          D ⊆ A + B ∧ A + B =ᵐ[loebMeasure U hU] D := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let C := e +ᵥ B
  have hCm : MeasurableSet C := by
    change MeasurableSet (e +ᵥ B)
    rw [vadd_set_eq_neg_preimage]
    exact hBm.preimage (measurable_add_left U hU (-e))
  have hCmass : μ C = μ B := loebMeasure_image_add_left U hU e B
  have hsum : A + C = e +ᵥ (A + B) := add_vadd_set_eq e A B
  have hsumM : MeasurableSet (A + C) := by
    rw [hsum, vadd_set_eq_neg_preimage]
    exact hSm.preimage (measurable_add_left U hU (-e))
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
  have hnotperiod' : ¬ ∃ H : AddSubgroup G, MeasurableSet (H : Set G) ∧
      0 < μ (H : Set G) ∧ (A + C) + (H : Set G) = A + C := by
    rintro ⟨H, hHm, hHpos, hper⟩
    apply hnotperiod
    refine ⟨H, hHm, hHpos, ?_⟩
    simp only [hsum, vadd_set_add_eq] at hper
    have h := congrArg (fun S => -e +ᵥ S) hper
    simpa only [neg_vadd_vadd] using h
  let H := AddAction.stabilizer G ((A ∪ C) + (A ∩ C))
  have hUpos : 0 < μ (A ∪ C) := hI.trans_le (measure_mono (inter_subset_left.trans subset_union_left))
  obtain ⟨_, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q (A ∪ C) (A ∩ C)
    (hAm.union hCm) (hAm.inter hCm) hUpos hI hsmall'
  obtain ⟨D, p, hDsub, hDae, _⟩ := loeb_strict_dyson_quasiPeriodic_output_model U hU q A C
    hAm hCm hsumM hI hfull' hsmall' hnotperiod'
  let R := -e +ᵥ D
  have hRsub : R ⊆ A + B := by
    have h : -e +ᵥ D ⊆ -e +ᵥ (A + C) := image_mono hDsub
    simpa only [hsum, neg_vadd_vadd] using h
  have hRae : A + B =ᵐ[μ] R := by
    have h := loeb_vadd_congr_ae U hU (A + C) D (-e) hDae
    simpa only [hsum, neg_vadd_vadd] using h
  exact ⟨H, hHm, hHpos, R, ⟨p.loebTranslate U hU (-e)⟩, hRsub, hRae⟩

end Erdos335.Loeb

end
