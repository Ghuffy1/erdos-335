import Erdos335.LoebMeasurableSetModel
import Erdos335.LoebCriticalContainer

/-!
# Reduction of irreducible Loeb equality pairs to compact equality pairs

If the measurable compact model has a strict sumset deficit, the Loeb
critical-container theorem gives a finite-period decomposition. In the
other case all input and sumset measures are exact, and the inputs agree
almost everywhere with compact-model pullbacks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem preimage_add_of_surjective_addHom
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (φ : G →+ K) (hφ : Function.Surjective φ) (C D : Set K) :
    φ ⁻¹' (C + D) = (φ ⁻¹' C) + (φ ⁻¹' D) := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨c, hc, d, hd, hcd⟩ := hx
    change c + d = φ x at hcd
    obtain ⟨a, ha⟩ := hφ c
    refine ⟨a, ?_, x - a, ?_, by abel⟩
    · change φ a ∈ C
      rwa [ha]
    · change φ (x - a) ∈ D
      have heq : φ (x - a) = d := by
        rw [map_sub, ha, ← hcd]
        exact add_sub_cancel_left c d
      rwa [heq]
  · rintro x ⟨a, ha, b, hb, rfl⟩
    change φ (a + b) ∈ C + D
    rw [map_add]
    exact add_mem_add ha hb

local instance compactEqualityLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U
local instance compactEqualityCircleSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance compactEqualityCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

def HasCompactEqualityModel
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) : Prop :=
  ∃ F : ℕ → ∀ n, ZMod (q n : ℕ) →+ Additive Circle,
    ∃ C D : Set (countableUltralimitHom U F).range,
      IsCompact ((countableUltralimitHom U F).range : Set (ℕ → Additive Circle)) ∧
      Measure.IsAddHaarMeasure
        (Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ∧
      IsSigmaCompact C ∧ IsSigmaCompact D ∧ MeasurableSet C ∧ MeasurableSet D ∧
      MeasurableSet (C + D) ∧
      Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) C = loebMeasure U hU A ∧
      Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) D = loebMeasure U hU B ∧
      Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) (C + D) =
        loebMeasure U hU A + loebMeasure U hU B ∧
      A =ᵐ[loebMeasure U hU] (countableUltralimitHom U F).rangeRestrict ⁻¹' C ∧
      B =ᵐ[loebMeasure U hU] (countableUltralimitHom U F).rangeRestrict ⁻¹' D ∧
      (∀ᵐ x ∂loebMeasure U hU,
        (countableUltralimitHom U F).rangeRestrict x ∈ C + D → x ∈ A + B)

theorem loeb_irreducible_equality_compact_or_decomposed
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B) :
    HasCompactEqualityModel U hU q A B ∨
      ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
        MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
        0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
        ((A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B ∨
          ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
            loebMeasure U hU p.left.active = 0 ∧ loebMeasure U hU p.right.active = 0) := by
  classical
  obtain ⟨F, C, D, hcompact, hhaar, hCsc, hDsc, hCm, hDm, hCDm,
      hCbound, hDbound, hApull, hBpull, hSumpull, hSumbound⟩ :=
    exists_compact_measurable_set_model U hU A B hAm hBm
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let π := (countableUltralimitHom U F).rangeRestrict
  let ν := Measure.map π μ
  let P := π ⁻¹' C
  let Q := π ⁻¹' D
  have hπ : Measurable π := (measurable_countableUltralimitHom U F).subtype_mk
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    exact ⟨x, Subtype.ext hx⟩
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hPm : MeasurableSet P := hCm.preimage hπ
  have hQm : MeasurableSet Q := hDm.preimage hπ
  have hPmass : μ P = ν C := (Measure.map_apply hπ hCm).symm
  have hQmass : μ Q = ν D := (Measure.map_apply hπ hDm).symm
  have hsum : P + Q = π ⁻¹' (C + D) := (preimage_add_of_surjective_addHom π hπsurj C D).symm
  have hPQm : MeasurableSet (P + Q) := by rw [hsum]; exact hCDm.preimage hπ
  have hsumMass : μ (P + Q) = ν (C + D) := by rw [hsum]; exact (Measure.map_apply hπ hCDm).symm
  have hsumInner : internalInnerMeasure U hU (P + Q) = ν (C + D) :=
    (internalInnerMeasure_eq U hU (P + Q) hPQm).trans hsumMass
  by_cases hstrict : ν (C + D) < ν C + ν D
  · right
    have hbound : internalInnerMeasure U hU (P + Q) ≤ internalInnerMeasure U hU (A + B) := by
      rw [hsumInner]
      exact hSumbound
    have hsmall : internalInnerMeasure U hU (P + Q) < μ P + μ Q := by
      rw [hsumInner, hPmass, hQmass]
      exact hstrict
    obtain ⟨hHm, hHpos, hresult⟩ := loeb_irreducible_pair_in_critical_container U hU q A B P Q
      hAm hBm hPm hQm hApos hBpos hirr hApull hBpull hfull hbound hsmall
    exact ⟨AddAction.stabilizer G (P + Q), hHm, hHpos, hresult⟩
  · left
    have hsumLower : ν C + ν D ≤ ν (C + D) := le_of_not_gt hstrict
    have hsumEq : ν (C + D) = μ A + μ B := by
      apply le_antisymm (hSumbound.trans_eq hfull)
      exact (add_le_add hCbound hDbound).trans hsumLower
    have hCeq : ν C = μ A := by
      apply le_antisymm ?_ hCbound
      apply (ENNReal.add_le_add_iff_right (measure_ne_top μ B)).mp
      exact (add_le_add le_rfl hDbound).trans (hsumLower.trans_eq hsumEq)
    have hDeq : ν D = μ B := by
      apply le_antisymm ?_ hDbound
      apply (ENNReal.add_le_add_iff_left (measure_ne_top μ A)).mp
      exact (add_le_add hCbound le_rfl).trans (hsumLower.trans_eq hsumEq)
    have hAinter : A ∩ P =ᵐ[μ] A := by
      filter_upwards [hApull] with x hx
      change x ∈ A → x ∈ P at hx
      apply propext
      simp only [mem_inter_iff]
      tauto
    have hBinter : B ∩ Q =ᵐ[μ] B := by
      filter_upwards [hBpull] with x hx
      change x ∈ B → x ∈ Q at hx
      apply propext
      simp only [mem_inter_iff]
      tauto
    have hPzero : μ (P \ (A ∩ P)) = 0 := by
      rw [measure_sdiff inter_subset_right (hAm.inter hPm).nullMeasurableSet (measure_ne_top μ _),
        measure_congr hAinter, hPmass, hCeq, tsub_self]
    have hQzero : μ (Q \ (B ∩ Q)) = 0 := by
      rw [measure_sdiff inter_subset_right (hBm.inter hQm).nullMeasurableSet (measure_ne_top μ _),
        measure_congr hBinter, hQmass, hDeq, tsub_self]
    have hAeq : A =ᵐ[μ] P :=
      hAinter.symm.trans (inter_subset_right.eventuallySubset.antisymm (ae_le_set.mpr hPzero))
    have hBeq : B =ᵐ[μ] Q :=
      hBinter.symm.trans (inter_subset_right.eventuallySubset.antisymm (ae_le_set.mpr hQzero))
    exact ⟨F, C, D, hcompact, hhaar, hCsc, hDsc, hCm, hDm, hCDm,
      hCeq, hDeq, hsumEq, hAeq, hBeq, hSumpull⟩

end Erdos335.Loeb

end
