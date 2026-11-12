import Erdos335.LoebCompactModelInverse
import Erdos335.LoebCompactEqualityReduction

/-!
# The irreducible aperiodic Loeb inverse theorem
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance irreducibleInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U
local instance irreducibleInverseCircleSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance irreducibleInverseCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem loeb_irreducible_aperiodic_quasiPeriodic_or_internalBohr
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) ∨
      Nonempty (InternalBohrPairData U hU q A B) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hcomp : 0 < μ (A + B)ᶜ :=
    loeb_complement_pos_of_no_positive_periods U hU q (A + B) hnoAE
  have hinner : internalInnerMeasure U hU (A + B) = μ A + μ B :=
    (internalInnerMeasure_eq U hU _ hSm).trans hfull
  rcases loeb_irreducible_equality_compact_or_decomposed U hU q A B hAm hBm hApos hBpos
    hirr hinner with hmodel | ⟨H, hHm, hHpos, hdecomposed⟩
  · obtain ⟨F, C, D, hcompact, hhaar, hCsc, hDsc, hCm, hDm, hCDm,
      hCmass, hDmass, hCDmass, hAmodel, hBmodel, hSbound⟩ := hmodel
    letI : CompactSpace (countableUltralimitHom U F).range := isCompact_iff_compactSpace.mp hcompact
    let φ := (countableUltralimitHom U F).rangeRestrict
    have hφ : Measurable φ := (measurable_countableUltralimitHom U F).subtype_mk
    have hmass : μ (φ ⁻¹' (C + D)) = μ (A + B) := by
      rw [← Measure.map_apply hφ hCDm, hCDmass, hfull]
    have hsumModel : φ ⁻¹' (C + D) =ᵐ[μ] A + B :=
      ae_eq_of_ae_subset_of_measure_ge hSbound hmass.ge (hCDm.preimage hφ).nullMeasurableSet
        (measure_ne_top μ (A + B))
    exact loeb_countable_model_quasiPeriodic_or_internalBohr U hU q F A B hAm hBm hSm
      hApos hBpos hcomp hfull hirr hne hnoAE C D hCsc hDsc hAmodel.symm hBmodel.symm hsumModel
  · rcases hdecomposed with hperiod | ⟨p, _, _⟩
    · exfalso
      apply hnoAE H hHm hHpos
      intro t ht
      exact loeb_translate_ae_of_essential_period U hU q (A + B) hSm H
        (ae_le_set.mp hperiod.le) t ht
    · exact Or.inl ⟨p⟩

end Erdos335.Loeb

end
