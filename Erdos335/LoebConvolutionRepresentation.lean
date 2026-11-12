import Erdos335.LoebConvolutionFactor
import Erdos335.MeasureFactorLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Measurable compact-factor representation of convolution

The continuous approximants on the common compact group converge in measure.
An almost-everywhere subsequential limit gives a measurable representative
on that compact Haar factor.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_compact_convolution_factor
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℂ) (hf : ∀ n x, ‖f n x‖ ≤ 1) (hg : ∀ n x, ‖g n x‖ ≤ 1) :
    ∃ F : ℕ → ∀ n, X n →+ Additive Circle,
      ∃ Q : (countableUltralimitHom U F).range → ℂ,
        StronglyMeasurable Q ∧
        IsCompact ((countableUltralimitHom U F).range : Set (ℕ → Additive Circle)) ∧
        Measure.IsAddHaarMeasure
          (@Measure.map _ _ (loebMeasurableSpace U) _
            (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ∧
        (fun x => ∫ t, boundedComplexFunction U f 1 hf t *
          boundedComplexFunction U g 1 hg (x - t) ∂loebMeasure U hU) =ᵐ[loebMeasure U hU]
            Q ∘ (countableUltralimitHom U F).rangeRestrict := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  obtain ⟨F, P, hP, hcompact, hhaar, herr⟩ :=
    exists_compact_convolution_approximations U hU f g hf hg
  let π := countableUltralimitHom U F
  letI : CompactSpace π.range := isCompact_iff_compactSpace.mp hcompact
  let H : (U : Filter ℕ).Product X → ℂ := fun x =>
    ∫ t, boundedComplexFunction U f 1 hf t * boundedComplexFunction U g 1 hg (x - t) ∂μ
  let R : ℕ → (U : Filter ℕ).Product X → ℂ := fun n x => P n (π.rangeRestrict x)
  have hq : Measurable π.rangeRestrict :=
    (measurable_countableUltralimitHom U F).subtype_mk
  have hH : MemLp H 2 μ := by
    have heq : H = boundedComplexFunction U (fun n => FiniteFourier.convolution (f n) (g n)) 1
        (fun n x => normalized_convolution_norm_le_one (f n) (g n) (hf n) (hg n) x) := by
      funext x
      exact (boundedComplex_convolution_eq U hU f g hf hg x).symm
    rw [heq]
    exact MemLp.of_bound (measurable_boundedComplexFunction U _ _ _).aestronglyMeasurable
      1 (ae_of_all μ (boundedComplexFunction_bound U _ _ _))
  have hRP (n : ℕ) : MemLp (R n) 2 μ := by
    let p : C(π.range, ℂ) := ⟨P n, hP n⟩
    exact MemLp.of_bound ((hP n).stronglyMeasurable.comp_measurable hq).aestronglyMeasurable
      ‖p‖ (ae_of_all μ (fun x => ContinuousMap.norm_coe_le_norm p (π.rangeRestrict x)))
  have hmem (n : ℕ) : MemLp (R n - H) 2 μ := (hRP n).sub hH
  have hupper (n : ℕ) : (∫ x, ‖R n x - H x‖ ^ 2 ∂μ) ≤ (1 / (n + 1 : ℝ)) ^ 2 := by
    calc
      (∫ x, ‖R n x - H x‖ ^ 2 ∂μ) = ∫ x, ‖H x - R n x‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ (fun x => congrArg (fun t : ℝ => t ^ 2) (norm_sub_rev _ _))
      _ ≤ _ := herr n
  have hrate : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : 2 ≠ 0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have hlim : Tendsto (fun n => ∫ x, ‖R n x - H x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) hupper hrate
  have hmeasure := tendstoInMeasure_of_sqIntegral_tendsto_zero μ R H hmem hlim
  obtain ⟨Q, hQ, hfactor⟩ := exists_factor_of_tendstoInMeasure μ π.rangeRestrict P H
    (fun n => (hP n).stronglyMeasurable) hmeasure
  exact ⟨F, Q, hQ, hcompact, hhaar, hfactor⟩

end Erdos335.Loeb

end
