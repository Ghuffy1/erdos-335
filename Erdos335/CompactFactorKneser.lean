import Erdos335.LoebCompactSubgroupImage
import Erdos335.StabilizerPullback
import Erdos335.LoebMeasurableKneserIdentity
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Kneser's identity in compact ultralimit factors

A strict inner-measure deficit in the cyclic Loeb pullback gives a positive
Loeb stabilizer. Its image is compact and open in the compact factor.
The exact Kneser identity then passes through the quotient map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance compactFactorKneserLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

variable {E : Type*} [AddCommGroup E] [MetricSpace E] [CompactSpace E]
  [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]

theorem compact_factor_kneser_from_pullback
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (f : ∀ n, ZMod (q n : ℕ) →+ E)
    (C D : Set (ultralimitAddHom U f).range)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCpos : 0 < Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU) D)
    (hsmall : internalInnerMeasure U hU
      (((ultralimitAddHom U f).rangeRestrict ⁻¹' C) +
        ((ultralimitAddHom U f).rangeRestrict ⁻¹' D)) <
      Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU) C +
        Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU) D) :
    let ν := Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU)
    let H := AddAction.stabilizer (ultralimitAddHom U f).range (C + D)
    IsCompact (H : Set (ultralimitAddHom U f).range) ∧
      IsOpen (H : Set (ultralimitAddHom U f).range) ∧
      0 < ν (H : Set (ultralimitAddHom U f).range) ∧ IsOpen (C + D) ∧
      ν (C + (H : Set (ultralimitAddHom U f).range)) +
        ν (D + (H : Set (ultralimitAddHom U f).range)) =
        ν (C + D) + ν (H : Set (ultralimitAddHom U f).range) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let φ := ultralimitAddHom U f
  let K := φ.range
  let π := φ.rangeRestrict
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map π μ
  let P := π ⁻¹' C
  let Q := π ⁻¹' D
  let L := AddAction.stabilizer G (P + Q)
  let H := AddAction.stabilizer K (C + D)
  have hπ : Measurable π := measurable_rangeRestrict_ultralimitAddHom U f
  have hsurj : Function.Surjective π := φ.rangeRestrict_surjective
  have hPmass : μ P = ν C := (Measure.map_apply hπ hC).symm
  have hQmass : μ Q = ν D := (Measure.map_apply hπ hD).symm
  have hPpos : 0 < μ P := hPmass.symm ▸ hCpos
  have hQpos : 0 < μ Q := hQmass.symm ▸ hDpos
  have hsmall' : internalInnerMeasure U hU (P + Q) < μ P + μ Q := by
    rw [hPmass, hQmass]
    exact hsmall
  obtain ⟨hPQm, hLm, hLpos, hid⟩ := loeb_measurable_kneser_identity U hU q P Q
    (hC.preimage hπ) (hD.preimage hπ) hPpos hQpos hsmall'
  have hsum : P + Q = π ⁻¹' (C + D) :=
    (preimage_add_of_surjective_addHom π hsurj C D).symm
  have hL : L = H.comap π := by
    change AddAction.stabilizer G (P + Q) = H.comap π
    rw [hsum]
    exact stabilizer_preimage_comap π hsurj (C + D)
  have hmap : L.map π = H := by
    rw [hL]
    exact AddSubgroup.map_comap_eq_self_of_surjective hsurj H
  have hHcompact : IsCompact (H : Set K) := by
    rw [← hmap]
    exact isCompact_image_positive_loeb_subgroup_rangeRestrict U hU q L hLm hLpos f
  have hHopen : IsOpen (H : Set K) := by
    rw [← hmap]
    exact isOpen_map_positive_loeb_subgroup_rangeRestrict U hU q L hLm hLpos f
  have hHmass : ν (H : Set K) = μ (L : Set G) := by
    rw [Measure.map_apply hπ hHopen.measurableSet]
    change μ (H.comap π : Set G) = μ (L : Set G)
    rw [hL]
  have hperiod : (C + D) + (H : Set K) = C + D := by
    apply subset_antisymm
    · rintro z ⟨s, hs, k, hk, rfl⟩
      have heq : k +ᵥ (C + D) = C + D := hk
      have hm : k + s ∈ C + D := by
        rw [← heq]
        exact ⟨s, hs, rfl⟩
      simpa only [add_comm s k] using hm
    · intro s hs
      exact ⟨s, hs, 0, H.zero_mem, add_zero s⟩
  have hSopen : IsOpen (C + D) := by
    rw [← hperiod]
    exact hHopen.add_left
  have hCmass : ν (C + (H : Set K)) = μ (P + (L : Set G)) := by
    rw [Measure.map_apply hπ hHopen.add_left.measurableSet,
      preimage_add_of_surjective_addHom π hsurj]
    change μ (P + (H.comap π : Set G)) = _
    rw [← hL]
  have hDmass : ν (D + (H : Set K)) = μ (Q + (L : Set G)) := by
    rw [Measure.map_apply hπ hHopen.add_left.measurableSet,
      preimage_add_of_surjective_addHom π hsurj]
    change μ (Q + (H.comap π : Set G)) = _
    rw [← hL]
  have hSmass : ν (C + D) = μ (P + Q) := by
    rw [Measure.map_apply hπ hSopen.measurableSet, ← hsum]
  refine ⟨hHcompact, hHopen, ?_, hSopen, ?_⟩
  · rw [hHmass]
    exact hLpos
  · rw [hCmass, hDmass, hSmass, hHmass]
    exact hid

theorem compact_factor_kneser_identity
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (f : ∀ n, ZMod (q n : ℕ) →+ E)
    (C D : Set (ultralimitAddHom U f).range)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hCD : MeasurableSet (C + D))
    (hCpos : 0 < Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU) D)
    (hsmall : Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU) (C + D) <
      Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU) C +
        Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU) D) :
    let ν := Measure.map (ultralimitAddHom U f).rangeRestrict (loebMeasure U hU)
    let H := AddAction.stabilizer (ultralimitAddHom U f).range (C + D)
    IsCompact (H : Set (ultralimitAddHom U f).range) ∧
      IsOpen (H : Set (ultralimitAddHom U f).range) ∧
      0 < ν (H : Set (ultralimitAddHom U f).range) ∧ IsOpen (C + D) ∧
      ν (C + (H : Set (ultralimitAddHom U f).range)) +
        ν (D + (H : Set (ultralimitAddHom U f).range)) =
        ν (C + D) + ν (H : Set (ultralimitAddHom U f).range) := by
  let π := (ultralimitAddHom U f).rangeRestrict
  have hπ : Measurable π := measurable_rangeRestrict_ultralimitAddHom U f
  apply compact_factor_kneser_from_pullback U hU q f C D hC hD hCpos hDpos
  rw [← preimage_add_of_surjective_addHom π (ultralimitAddHom U f).rangeRestrict_surjective,
    internalInnerMeasure_eq U hU _ (hCD.preimage hπ)]
  rwa [← Measure.map_apply hπ hCD]

end Erdos335.Loeb

end
