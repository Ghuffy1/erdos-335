import Erdos335.LoebCompactModel
import Erdos335.CompactSetRegularization

/-!
# Compact set models for two internal sets

The positive convolution model and compact set regularization produce a
compact Haar factor with measurable sumsets. Both original internal sets
lie in the pullbacks of the model sets almost everywhere, and the pullback
of the model sum lies in the original internal sum almost everywhere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance setModelLoebMeasurableSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance setModelCircleMeasurableSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance setModelCircleBorelSpace : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_compact_internal_set_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (A B : ∀ n, Set (X n)) :
    ∃ F : ℕ → ∀ n, X n →+ Additive Circle,
      ∃ C D : Set (countableUltralimitHom U F).range,
        IsCompact ((countableUltralimitHom U F).range : Set (ℕ → Additive Circle)) ∧
        Measure.IsAddHaarMeasure
          (Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ∧
        IsSigmaCompact C ∧ IsSigmaCompact D ∧
        MeasurableSet C ∧ MeasurableSet D ∧
        MeasurableSet (C + D) ∧
        ultraCount U A ≤ Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) C ∧
        ultraCount U B ≤ Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) D ∧
        (∀ᵐ x ∂loebMeasure U hU,
          x ∈ internalSet U A → (countableUltralimitHom U F).rangeRestrict x ∈ C) ∧
        (∀ᵐ x ∂loebMeasure U hU,
          x ∈ internalSet U B → (countableUltralimitHom U F).rangeRestrict x ∈ D) ∧
        (∀ᵐ x ∂loebMeasure U hU,
          (countableUltralimitHom U F).rangeRestrict x ∈ C + D →
            x ∈ internalSet U (fun n => A n + B n)) ∧
        Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) (C + D) ≤
          ultraCount U (fun n => A n + B n) := by
  let f (n : ℕ) := (A n).indicator (fun _ => (1 : ℝ))
  let g (n : ℕ) := (B n).indicator (fun _ => (1 : ℝ))
  have hf (n : ℕ) (x : X n) : |f n x| ≤ 1 := indicator_one_abs_le (A n) x
  have hg (n : ℕ) (x : X n) : |g n x| ≤ 1 := indicator_one_abs_le (B n) x
  have hf01 (n : ℕ) (x : X n) : f n x ∈ Icc (0 : ℝ) 1 := by
    classical
    by_cases hx : x ∈ A n <;> simp [f, hx]
  have hg01 (n : ℕ) (x : X n) : g n x ∈ Icc (0 : ℝ) 1 := by
    classical
    by_cases hx : x ∈ B n <;> simp [g, hx]
  obtain ⟨F, a, b, hcompact, hhaar, ha, hb, hab01, hsupport, hmassA, hmassB, hrep⟩ :=
    exists_compact_positive_convolution_model U hU f g hf hg hf01 hg01
  letI : MetricSpace (ℕ → Additive Circle) := PiCountable.metricSpace
  letI : CompactSpace (countableUltralimitHom U F).range := isCompact_iff_compactSpace.mp hcompact
  let μ := loebMeasure (X := X) U hU
  let q := (countableUltralimitHom U F).rangeRestrict
  let ν := Measure.map q μ
  have hq : Measurable q := (measurable_countableUltralimitHom U F).subtype_mk
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  letI : IsProbabilityMeasure ν := ⟨by
    change Measure.map q μ univ = 1
    rw [Measure.map_apply hq MeasurableSet.univ]
    simp⟩
  letI : Measure.IsAddHaarMeasure ν := hhaar
  obtain ⟨C, D, hCsc, hDsc, hCm, hDm, hCsub, hDsub, hCmass, hDmass, hCDsc, hCDm, hCDpos⟩ :=
    exists_positive_support_sigmaCompact_representatives ν a b ha.measurable hb.measurable
      (fun x => (hab01 x).1) (fun x => (hab01 x).2)
  have hCeq : C =ᵐ[ν] {x | 0 < a x} :=
    ae_eq_of_subset_of_measure_ge hCsub hCmass.ge hCm.nullMeasurableSet (measure_ne_top ν _)
  have hDeq : D =ᵐ[ν] {x | 0 < b x} :=
    ae_eq_of_subset_of_measure_ge hDsub hDmass.ge hDm.nullMeasurableSet (measure_ne_top ν _)
  have hApull : ∀ᵐ x ∂μ, x ∈ internalSet U A → q x ∈ C := by
    filter_upwards [hsupport, ae_of_ae_map hq.aemeasurable hCeq] with x hx hc
    intro hxA
    have hfx : 0 < boundedRealFunction U f 1 hf x := by
      change 0 < boundedRealFunction U (fun n => (A n).indicator (fun _ => (1 : ℝ))) 1 hf x
      rw [boundedRealFunction_indicator]
      simp [hxA]
    exact hc.mpr (hx.1 hfx)
  have hBpull : ∀ᵐ x ∂μ, x ∈ internalSet U B → q x ∈ D := by
    filter_upwards [hsupport, ae_of_ae_map hq.aemeasurable hDeq] with x hx hd
    intro hxB
    have hgx : 0 < boundedRealFunction U g 1 hg x := by
      change 0 < boundedRealFunction U (fun n => (B n).indicator (fun _ => (1 : ℝ))) 1 hg x
      rw [boundedRealFunction_indicator]
      simp [hxB]
    exact hd.mpr (hx.2 hgx)
  have hSumpull : ∀ᵐ x ∂μ, q x ∈ C + D → x ∈ internalSet U (fun n => A n + B n) := by
    filter_upwards [hrep] with x hx
    intro hsum
    apply positive_internal_convolution_subset_add U hU A B
    change 0 < ∫ t, boundedRealFunction U f 1 hf t * boundedRealFunction U g 1 hg (x - t) ∂μ
    rw [hx]
    exact hCDpos hsum
  have hCbound : ultraCount U A ≤ ν C := by
    rw [show ν C = μ (q ⁻¹' C) from Measure.map_apply hq hCm]
    rw [← loebMeasure_internal U hU A]
    exact measure_mono_ae hApull
  have hDbound : ultraCount U B ≤ ν D := by
    rw [show ν D = μ (q ⁻¹' D) from Measure.map_apply hq hDm]
    rw [← loebMeasure_internal U hU B]
    exact measure_mono_ae hBpull
  have hSumbound : ν (C + D) ≤ ultraCount U (fun n => A n + B n) := by
    rw [show ν (C + D) = μ (q ⁻¹' (C + D)) from Measure.map_apply hq hCDm]
    rw [← loebMeasure_internal U hU (fun n => A n + B n)]
    exact measure_mono_ae hSumpull
  exact ⟨F, C, D, hcompact, hhaar, hCsc, hDsc, hCm, hDm, hCDm,
    hCbound, hDbound, hApull, hBpull, hSumpull, hSumbound⟩

end Erdos335.Loeb

end
