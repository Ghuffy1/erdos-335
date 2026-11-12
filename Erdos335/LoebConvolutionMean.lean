import Erdos335.LoebMeasurableSetModel
import Erdos335.CompactConvolutionContinuity
import Erdos335.CompactFourierConvolution

/-!
# The mean of a measurable Loeb convolution

The compact convolution factor transfers the integral identity from Haar
measure to arbitrary measurable Loeb inputs. Positive input measures
therefore give a point with positive convolution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance convolutionMeanLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance convolutionMeanCircleSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance convolutionMeanCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem loeb_integral_indicator_convolution
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X)) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (∫ x, ∫ t, A.indicator (fun _ => (1 : ℝ)) t *
      B.indicator (fun _ => (1 : ℝ)) (x - t) ∂loebMeasure U hU ∂loebMeasure U hU) =
        (loebMeasure U hU A).toReal * (loebMeasure U hU B).toReal := by
  classical
  obtain ⟨Ai, hAi⟩ := exists_internal_ae_representative U hU A hAm
  obtain ⟨Bi, hBi⟩ := exists_internal_ae_representative U hU B hBm
  let f (n : ℕ) := (Ai n).indicator (fun _ => (1 : ℝ))
  let g (n : ℕ) := (Bi n).indicator (fun _ => (1 : ℝ))
  have hf (n : ℕ) (x : X n) : |f n x| ≤ 1 := indicator_one_abs_le (Ai n) x
  have hg (n : ℕ) (x : X n) : |g n x| ≤ 1 := indicator_one_abs_le (Bi n) x
  have hf01 (n : ℕ) (x : X n) : f n x ∈ Icc (0 : ℝ) 1 := by
    by_cases hx : x ∈ Ai n <;> simp [f, hx]
  have hg01 (n : ℕ) (x : X n) : g n x ∈ Icc (0 : ℝ) 1 := by
    by_cases hx : x ∈ Bi n <;> simp [g, hx]
  obtain ⟨F, a, b, hcompact, hhaar, ha, hb, hab01, _, hamean, hbmean, hrep⟩ :=
    exists_compact_positive_convolution_model U hU f g hf hg hf01 hg01
  let : MetricSpace (ℕ → Additive Circle) := PiCountable.metricSpace
  let : CompactSpace (countableUltralimitHom U F).range := isCompact_iff_compactSpace.mp hcompact
  let μ := loebMeasure (X := X) U hU
  let π := (countableUltralimitHom U F).rangeRestrict
  let ν := Measure.map π μ
  have hπ : Measurable π := (measurable_countableUltralimitHom U F).subtype_mk
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map π μ univ = 1
    rw [Measure.map_apply hπ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure ν := hhaar
  have hneg : Measure.map (fun x : (U : Filter ℕ).Product X => -x) μ = μ := by
    simpa only [zero_sub] using (loebMeasurePreserving_sub_left U hU (0 : (U : Filter ℕ).Product X)).map_eq
  have hnegm : Measurable (fun x : (U : Filter ℕ).Product X => -x) := by
    simpa only [zero_sub] using (loebMeasurePreserving_sub_left U hU (0 : (U : Filter ℕ).Product X)).measurable
  have : ν.IsNegInvariant := by
    constructor
    change Measure.map Neg.neg (Measure.map π μ) = Measure.map π μ
    rw [Measure.map_map measurable_neg hπ]
    have hcomp : Neg.neg ∘ π = π ∘ (fun x : (U : Filter ℕ).Product X => -x) := by
      funext x
      exact (map_neg π x).symm
    rw [hcomp, ← Measure.map_map hπ hnegm, hneg]
  have habound (y) : ‖a y‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg (hab01 y).1.1] using (hab01 y).1.2
  have hbbound (y) : ‖b y‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg (hab01 y).2.1] using (hab01 y).2.2
  have hai : Integrable a ν := Integrable.of_bound ha.aestronglyMeasurable 1 (ae_of_all ν habound)
  have hbi : Integrable b ν := Integrable.of_bound hb.aestronglyMeasurable 1 (ae_of_all ν hbbound)
  have hcontinuous := continuous_bounded_real_convolution ν a b ha.measurable hb.measurable habound hbbound
  have haIntegral : (∫ y, a y ∂ν) = (μ A).toReal := by
    calc
      (∫ y, a y ∂ν) = ∫ t, (internalSet U Ai).indicator (fun _ => (1 : ℝ)) t ∂μ := by
        simpa only [f, boundedRealFunction_indicator] using hamean
      _ = (μ (internalSet U Ai)).toReal := by
        rw [integral_indicator (measurable_internalSet U Ai)]
        simp [measureReal_def]
      _ = (μ A).toReal := congrArg ENNReal.toReal (measure_congr hAi)
  have hbIntegral : (∫ y, b y ∂ν) = (μ B).toReal := by
    calc
      (∫ y, b y ∂ν) = ∫ t, (internalSet U Bi).indicator (fun _ => (1 : ℝ)) t ∂μ := by
        simpa only [g, boundedRealFunction_indicator] using hbmean
      _ = (μ (internalSet U Bi)).toReal := by
        rw [integral_indicator (measurable_internalSet U Bi)]
        simp [measureReal_def]
      _ = (μ B).toReal := congrArg ENNReal.toReal (measure_congr hBi)
  have hrep' : (fun x => ∫ t, A.indicator (fun _ => (1 : ℝ)) t *
        B.indicator (fun _ => (1 : ℝ)) (x - t) ∂μ) =ᵐ[μ]
      (fun x => ∫ t, a t * b (π x - t) ∂ν) := by
    have hrepI : (fun x => ∫ t, (internalSet U Ai).indicator (fun _ => (1 : ℝ)) t *
        (internalSet U Bi).indicator (fun _ => (1 : ℝ)) (x - t) ∂μ) =ᵐ[μ]
        (fun x => ∫ t, a t * b (π x - t) ∂ν) := by
      simpa only [f, g, boundedRealFunction_indicator] using hrep
    filter_upwards [hrepI] with x hx
    exact (loeb_indicator_convolution_congr_ae U hU (internalSet U Ai) A
      (internalSet U Bi) B hAi hBi x).symm.trans hx
  calc
    (∫ x, ∫ t, A.indicator (fun _ => (1 : ℝ)) t * B.indicator (fun _ => (1 : ℝ)) (x - t) ∂μ ∂μ) =
        ∫ x, ∫ t, a t * b (π x - t) ∂ν ∂μ := integral_congr_ae hrep'
    _ = ∫ y, ∫ t, a t * b (y - t) ∂ν ∂ν :=
      (integral_map hπ.aemeasurable hcontinuous.aestronglyMeasurable).symm
    _ = (∫ y, a y ∂ν) * ∫ y, b y ∂ν := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hai hbi
    _ = (μ A).toReal * (μ B).toReal := by rw [haIntegral, hbIntegral]

theorem loeb_exists_positive_indicator_convolution
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X)) (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B) :
    ∃ x, 0 < ∫ t, A.indicator (fun _ => (1 : ℝ)) t *
      B.indicator (fun _ => (1 : ℝ)) (x - t) ∂loebMeasure U hU := by
  have : IsProbabilityMeasure (loebMeasure (X := X) U hU) := isProbabilityMeasure_loebMeasure U hU
  by_contra hn
  push Not at hn
  have hnonpos := integral_nonpos_of_ae (ae_of_all (loebMeasure U hU) hn)
  rw [loeb_integral_indicator_convolution U hU A B hAm hBm] at hnonpos
  exact (not_le_of_gt (mul_pos (ENNReal.toReal_pos hApos.ne' (measure_ne_top _ A))
    (ENNReal.toReal_pos hBpos.ne' (measure_ne_top _ B)))) hnonpos

end Erdos335.Loeb

end
