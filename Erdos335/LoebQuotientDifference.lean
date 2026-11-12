import Erdos335.LoebDifferenceDeficit
import Erdos335.LoebStructurePullback

/-!
# Difference-set measure in a nonperiodic quotient model

The cyclic Loeb Kneser theorem supplies the difference-set lower bound
needed by the compact e-transform argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem preimage_neg_addHom
    {G K : Type*} [AddCommGroup G] [AddCommGroup K] (φ : G →+ K) (D : Set K) :
    φ ⁻¹' (-D) = -(φ ⁻¹' D) := by
  ext x
  change -φ x ∈ D ↔ φ (-x) ∈ D
  rw [map_neg]

local instance quotientDifferenceLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loebMeasure_map_hom_isNegInvariant
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [MeasurableSpace K] [MeasurableNeg K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) :
    (Measure.map φ (loebMeasure U hU)).IsNegInvariant := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hneg : Measure.map (fun x : G => -x) μ = μ := by
    simpa only [zero_sub] using
      (loebMeasurePreserving_sub_left (X := fun n => ZMod (q n : ℕ)) U hU (0 : G)).map_eq
  constructor
  change Measure.map Neg.neg (Measure.map φ μ) = Measure.map φ μ
  rw [Measure.map_map measurable_neg hφ]
  have hcomp : Neg.neg ∘ φ = φ ∘ (fun x : G => -x) := by
    funext x
    exact (map_neg φ x).symm
  rw [hcomp, ← Measure.map_map hφ (measurable_loeb_neg U hU), hneg]

theorem loeb_quotient_difference_measure_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [MeasurableSpace K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set K) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hDiff : MeasurableSet (C + (-D)))
    (hCpos : 0 < Measure.map φ (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map φ (loebMeasure U hU) D)
    (hnotperiod : ¬ ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      ((φ ⁻¹' C) + (φ ⁻¹' D)) + (H : Set _) = (φ ⁻¹' C) + (φ ⁻¹' D)) :
    Measure.map φ (loebMeasure U hU) C + Measure.map φ (loebMeasure U hU) D ≤
      Measure.map φ (loebMeasure U hU) (C + (-D)) := by
  by_contra hbound
  have hsmall := lt_of_not_ge hbound
  let P := φ ⁻¹' C
  let Q := φ ⁻¹' D
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have hPmass : μ P = ν C := (Measure.map_apply hφ hC).symm
  have hQmass : μ Q = ν D := (Measure.map_apply hφ hD).symm
  have hPpos : 0 < μ P := hPmass.symm ▸ hCpos
  have hQpos : 0 < μ Q := hQmass.symm ▸ hDpos
  have hset : P + (-Q) = φ ⁻¹' (C + (-D)) := by
    rw [preimage_add_of_surjective_addHom φ hsurj, preimage_neg_addHom]
  have hinner : internalInnerMeasure U hU (P + (-Q)) = ν (C + (-D)) := by
    rw [hset, internalInnerMeasure_eq U hU _ (hDiff.preimage hφ), Measure.map_apply hφ hDiff]
  have hsmall' : internalInnerMeasure U hU (P + (-Q)) < μ P + μ Q := by
    rw [hinner, hPmass, hQmass]
    exact hsmall
  exact hnotperiod (loeb_difference_deficit_periodizes_sum U hU q P Q
    (hC.preimage hφ) (hD.preimage hφ) hPpos hQpos hsmall')

end Erdos335.Loeb

end
