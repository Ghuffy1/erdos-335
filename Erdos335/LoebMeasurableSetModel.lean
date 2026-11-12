import Erdos335.LoebInternalRepresentative
import Erdos335.LoebConvolutionAE
import Erdos335.LoebSetModel

/-!
# Compact Haar models for arbitrary measurable Loeb summands

Internal representatives and invariance of convolution under null
changes extend the internal-set model to measurable inputs. The model
sum is bounded by the inner measure of the literal original sum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance measurableSetModelLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance measurableSetModelCircleSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance measurableSetModelCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem loeb_inner_measure_ge_of_ae_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (D S : Set ((U : Filter ℕ).Product X)) (hDm : MeasurableSet D)
    (hDS : D ≤ᵐ[loebMeasure U hU] S) :
    loebMeasure U hU D ≤ internalInnerMeasure U hU S := by
  have hzero : loebMeasure U hU (D \ S) = 0 := ae_le_set.mp hDS
  have hNm := measurable_of_loebMeasure_zero U hU (D \ S) hzero
  have hMset : D ∩ S = D \ (D \ S) := by
    ext x
    simp only [mem_inter_iff, Set.mem_sdiff]
    tauto
  have hMm : MeasurableSet (D ∩ S) := by rw [hMset]; exact hDm.diff hNm
  have hAE : D ∩ S =ᵐ[loebMeasure U hU] D := by
    filter_upwards [hDS] with x hx
    change x ∈ D → x ∈ S at hx
    apply propext
    simp only [mem_inter_iff]
    tauto
  calc
    loebMeasure U hU D = loebMeasure U hU (D ∩ S) := (measure_congr hAE).symm
    _ = internalInnerMeasure U hU (D ∩ S) := (internalInnerMeasure_eq U hU _ hMm).symm
    _ ≤ internalInnerMeasure U hU S := internalInnerMeasure_mono U hU inter_subset_right

theorem exists_compact_measurable_set_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X)) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    ∃ F : ℕ → ∀ n, X n →+ Additive Circle,
      ∃ C D : Set (countableUltralimitHom U F).range,
        IsCompact ((countableUltralimitHom U F).range : Set (ℕ → Additive Circle)) ∧
        Measure.IsAddHaarMeasure
          (Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ∧
        IsSigmaCompact C ∧ IsSigmaCompact D ∧ MeasurableSet C ∧ MeasurableSet D ∧
        MeasurableSet (C + D) ∧
        loebMeasure U hU A ≤ Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) C ∧
        loebMeasure U hU B ≤ Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) D ∧
        (∀ᵐ x ∂loebMeasure U hU,
          x ∈ A → (countableUltralimitHom U F).rangeRestrict x ∈ C) ∧
        (∀ᵐ x ∂loebMeasure U hU,
          x ∈ B → (countableUltralimitHom U F).rangeRestrict x ∈ D) ∧
        (∀ᵐ x ∂loebMeasure U hU,
          (countableUltralimitHom U F).rangeRestrict x ∈ C + D → x ∈ A + B) ∧
        Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) (C + D) ≤
          internalInnerMeasure U hU (A + B) := by
  obtain ⟨Ai, hAi⟩ := exists_internal_ae_representative U hU A hAm
  obtain ⟨Bi, hBi⟩ := exists_internal_ae_representative U hU B hBm
  let f (n : ℕ) := (Ai n).indicator (fun _ => (1 : ℝ))
  let g (n : ℕ) := (Bi n).indicator (fun _ => (1 : ℝ))
  have hf (n : ℕ) (x : X n) : |f n x| ≤ 1 := indicator_one_abs_le (Ai n) x
  have hg (n : ℕ) (x : X n) : |g n x| ≤ 1 := indicator_one_abs_le (Bi n) x
  have hf01 (n : ℕ) (x : X n) : f n x ∈ Icc (0 : ℝ) 1 := by
    classical
    by_cases hx : x ∈ Ai n <;> simp [f, hx]
  have hg01 (n : ℕ) (x : X n) : g n x ∈ Icc (0 : ℝ) 1 := by
    classical
    by_cases hx : x ∈ Bi n <;> simp [g, hx]
  obtain ⟨F, a, b, hcompact, hhaar, ha, hb, hab01, hsupport, _, _, hrep⟩ :=
    exists_compact_positive_convolution_model U hU f g hf hg hf01 hg01
  letI : MetricSpace (ℕ → Additive Circle) := PiCountable.metricSpace
  letI : CompactSpace (countableUltralimitHom U F).range := isCompact_iff_compactSpace.mp hcompact
  let μ := loebMeasure (X := X) U hU
  let π := (countableUltralimitHom U F).rangeRestrict
  let ν := Measure.map π μ
  have hπ : Measurable π := (measurable_countableUltralimitHom U F).subtype_mk
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  letI : IsProbabilityMeasure ν := ⟨by
    change Measure.map π μ univ = 1
    rw [Measure.map_apply hπ MeasurableSet.univ]
    simp⟩
  letI : Measure.IsAddHaarMeasure ν := hhaar
  obtain ⟨C, D, hCsc, hDsc, hCm, hDm, hCsub, hDsub, hCmass, hDmass, _, hCDm, hCDpos⟩ :=
    exists_positive_support_sigmaCompact_representatives ν a b ha.measurable hb.measurable
      (fun x => (hab01 x).1) (fun x => (hab01 x).2)
  have hCeq : C =ᵐ[ν] {x | 0 < a x} :=
    ae_eq_of_subset_of_measure_ge hCsub hCmass.ge hCm.nullMeasurableSet (measure_ne_top ν _)
  have hDeq : D =ᵐ[ν] {x | 0 < b x} :=
    ae_eq_of_subset_of_measure_ge hDsub hDmass.ge hDm.nullMeasurableSet (measure_ne_top ν _)
  have hApull : ∀ᵐ x ∂μ, x ∈ A → π x ∈ C := by
    filter_upwards [hsupport, ae_of_ae_map hπ.aemeasurable hCeq, hAi] with x hx hc hi
    intro hxA
    have hxAi : x ∈ internalSet U Ai := hi.mpr hxA
    have hfx : 0 < boundedRealFunction U f 1 hf x := by
      change 0 < boundedRealFunction U (fun n => (Ai n).indicator (fun _ => (1 : ℝ))) 1 hf x
      rw [boundedRealFunction_indicator]
      simp [hxAi]
    exact hc.mpr (hx.1 hfx)
  have hBpull : ∀ᵐ x ∂μ, x ∈ B → π x ∈ D := by
    filter_upwards [hsupport, ae_of_ae_map hπ.aemeasurable hDeq, hBi] with x hx hd hi
    intro hxB
    have hxBi : x ∈ internalSet U Bi := hi.mpr hxB
    have hgx : 0 < boundedRealFunction U g 1 hg x := by
      change 0 < boundedRealFunction U (fun n => (Bi n).indicator (fun _ => (1 : ℝ))) 1 hg x
      rw [boundedRealFunction_indicator]
      simp [hxBi]
    exact hd.mpr (hx.2 hgx)
  have hrep' : (fun x => ∫ t, (internalSet U Ai).indicator (fun _ => (1 : ℝ)) t *
      (internalSet U Bi).indicator (fun _ => (1 : ℝ)) (x - t) ∂μ) =ᵐ[μ]
        (fun x => ∫ t, a t * b (π x - t) ∂ν) := by
    simpa only [f, g, boundedRealFunction_indicator] using hrep
  have hSumpull : ∀ᵐ x ∂μ, π x ∈ C + D → x ∈ A + B :=
    loeb_positive_model_subset_of_ae_variants U hU (internalSet U Ai) A (internalSet U Bi) B
      hAi hBi π C D (fun y => ∫ t, a t * b (y - t) ∂ν) (fun _ hy => hCDpos hy) hrep'
  have hCbound : μ A ≤ ν C := by
    rw [show ν C = μ (π ⁻¹' C) from Measure.map_apply hπ hCm]
    exact measure_mono_ae hApull
  have hDbound : μ B ≤ ν D := by
    rw [show ν D = μ (π ⁻¹' D) from Measure.map_apply hπ hDm]
    exact measure_mono_ae hBpull
  have hSumbound : ν (C + D) ≤ internalInnerMeasure U hU (A + B) := by
    rw [show ν (C + D) = μ (π ⁻¹' (C + D)) from Measure.map_apply hπ hCDm]
    exact loeb_inner_measure_ge_of_ae_subset U hU (π ⁻¹' (C + D)) (A + B) (hCDm.preimage hπ) hSumpull
  exact ⟨F, C, D, hcompact, hhaar, hCsc, hDsc, hCm, hDm, hCDm,
    hCbound, hDbound, hApull, hBpull, hSumpull, hSumbound⟩

end Erdos335.Loeb

end
