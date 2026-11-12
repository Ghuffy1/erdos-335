import Erdos335.LoebMeasurableKneserIdentity
import Erdos335.LoebFullInner

/-!
# Extendible equality pairs have an essential finite period

If enlarging the summands increases their total measure and preserves the
inner measure of the sum, the enlarged pair has a strict Kneser deficit.
Its period descends to the original measurable sum up to a null set.
The final theorem supplies measurability from the inner-measure equality.
This proves the cyclic Loeb version of Griesmer's Lemma 10.8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance extendibleLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem extendible_equality_pair_has_essential_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hCm : MeasurableSet (A + B))
    (hA'm : MeasurableSet A') (hB'm : MeasurableSet B')
    (hA : A ⊆ A') (hB : B ⊆ B')
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hequality : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hextra : loebMeasure U hU A + loebMeasure U hU B < loebMeasure U hU A' + loebMeasure U hU B')
    (hsame : internalInnerMeasure U hU (A' + B') = loebMeasure U hU (A + B)) :
    ∃ h : ℕ+, (A + B + (naturalCyclicKernel U q h : Set _)) =ᵐ[loebMeasure U hU] (A + B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hsmall : internalInnerMeasure U hU (A' + B') < μ A' + μ B' := by
    rw [hsame, hequality]
    exact hextra
  obtain ⟨h, _, _, hperiod⟩ := loeb_measurable_subcritical_period U hU q A' B' hA'm hB'm
    (hApos.trans_le (measure_mono hA)) (hBpos.trans_le (measure_mono hB)) hsmall
  let H := naturalCyclicKernel U q h
  obtain ⟨C', hC'⟩ := exists_internalSet_of_natural_kernel_period U q h (A' + B') hperiod
  have hC'm : MeasurableSet (A' + B') := by rw [← hC']; exact measurable_internalSet U _
  have hmass : μ (A' + B') = μ (A + B) := by
    rw [← internalInnerMeasure_eq U hU (A' + B') hC'm]
    exact hsame
  have hsub : A + B ⊆ A' + B' := add_subset_add hA hB
  have hnull : μ ((A' + B') \ (A + B)) = 0 := by
    rw [measure_sdiff hsub hCm.nullMeasurableSet (measure_ne_top μ _), hmass, tsub_self]
  have hperiodSub : (A + B) + (H : Set G) ⊆ A' + B' := by
    intro x hx
    have hx' := (add_subset_add hsub (show (H : Set G) ⊆ H from Subset.rfl)) hx
    rwa [hperiod] at hx'
  have hzero : μ (((A + B) + (H : Set G)) \ (A + B)) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left hperiodSub) hnull
  have hback : A + B ⊆ (A + B) + (H : Set G) := by
    intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  exact ⟨h, (ae_le_set.mpr hzero).antisymm hback.eventuallySubset⟩

theorem extendible_inner_equality_pair_has_essential_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hA'm : MeasurableSet A') (hB'm : MeasurableSet B')
    (hA : A ⊆ A') (hB : B ⊆ B')
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hequality : internalInnerMeasure U hU (A + B) =
      loebMeasure U hU A + loebMeasure U hU B)
    (hextra : loebMeasure U hU A + loebMeasure U hU B <
      loebMeasure U hU A' + loebMeasure U hU B')
    (hsame : internalInnerMeasure U hU (A' + B') = internalInnerMeasure U hU (A + B)) :
    MeasurableSet (A + B) ∧
      ∃ h : ℕ+, (A + B + (naturalCyclicKernel U q h : Set _)) =ᵐ[loebMeasure U hU] (A + B) := by
  have hsmall : internalInnerMeasure U hU (A' + B') <
      loebMeasure U hU A' + loebMeasure U hU B' := by
    rw [hsame, hequality]
    exact hextra
  obtain ⟨h, _, _, hperiod⟩ := loeb_measurable_subcritical_period U hU q A' B' hA'm hB'm
    (hApos.trans_le (measure_mono hA)) (hBpos.trans_le (measure_mono hB)) hsmall
  obtain ⟨C', hC'⟩ := exists_internalSet_of_natural_kernel_period U q h (A' + B') hperiod
  have hC'm : MeasurableSet (A' + B') := by rw [← hC']; exact measurable_internalSet U _
  have hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU (A' + B') :=
    hsame.symm.trans (internalInnerMeasure_eq U hU (A' + B') hC'm)
  have hCm := (measurable_of_subset_full_inner U hU (A + B) (A' + B')
    (add_subset_add hA hB) hC'm hfull).1
  have hequality' : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B :=
    (internalInnerMeasure_eq U hU (A + B) hCm).symm.trans hequality
  have hsame' : internalInnerMeasure U hU (A' + B') = loebMeasure U hU (A + B) :=
    hsame.trans (internalInnerMeasure_eq U hU (A + B) hCm)
  exact ⟨hCm, extendible_equality_pair_has_essential_period U hU q A B A' B'
    hAm hBm hCm hA'm hB'm hA hB hApos hBpos hequality' hextra hsame'⟩

end Erdos335.Loeb

end
