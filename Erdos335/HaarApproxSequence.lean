import Erdos335.HaarApproximation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A common almost-everywhere approximation by local averages

The two orientations use the same sequence of neighborhoods. The first
input is averaged at `u + x` and the second at `-u + x`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

theorem exists_common_local_average_ae
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsOpenPosMeasure]
    (f g : G → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfC : ∀ x, ‖f x‖ ≤ 1) (hgC : ∀ x, ‖g x‖ ≤ 1) :
    ∃ U : ℕ → Set G,
      (∀ n, IsOpen (U n) ∧ 0 ∈ U n ∧ 0 < μ (U n)) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => ∫ u, f (u + x) ∂((μ (U n))⁻¹ • μ.restrict (U n)))
        atTop (𝓝 (f x))) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => ∫ u, g (-u + x) ∂((μ (U n))⁻¹ • μ.restrict (U n)))
        atTop (𝓝 (g x))) := by
  choose U hUopen hUzero hUpos hUerrF hUerrG using
    (fun n : ℕ => exists_common_local_average μ f g hf hg 1 hfC hgC
      (1 / ((n : ℝ) + 1)) (by positivity))
  let ν (n : ℕ) := (μ (U n))⁻¹ • μ.restrict (U n)
  have hν (n : ℕ) : IsProbabilityMeasure (ν n) :=
    isProbabilityMeasure_normalized_restrict μ (U n) (hUpos n)
  let F (n : ℕ) (x : G) := ∫ u, f (u + x) ∂ν n
  let H (n : ℕ) (x : G) := ∫ u, g (-u + x) ∂ν n
  have hFm (n : ℕ) : StronglyMeasurable (F n) := by
    letI := hν n
    exact (show StronglyMeasurable (fun p : G × G => f (p.2 + p.1)) from
      (hf.comp (measurable_snd.add measurable_fst)).stronglyMeasurable).integral_prod_right'
  have hHm (n : ℕ) : StronglyMeasurable (H n) := by
    letI := hν n
    exact (show StronglyMeasurable (fun p : G × G => g (-p.2 + p.1)) from
      (hg.comp (measurable_snd.neg.add measurable_fst)).stronglyMeasurable).integral_prod_right'
  have hFi (n : ℕ) : Integrable (F n - f) μ := by
    letI := hν n
    apply (Integrable.of_bound (hFm n).aestronglyMeasurable 1 ?_).sub
      (Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all μ hfC))
    exact ae_of_all μ (fun x => by
      simpa only [F, probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (ae_of_all (ν n) (fun u => hfC (u + x))))
  have hHi (n : ℕ) : Integrable (H n - g) μ := by
    letI := hν n
    apply (Integrable.of_bound (hHm n).aestronglyMeasurable 1 ?_).sub
      (Integrable.of_bound hg.aestronglyMeasurable 1 (ae_of_all μ hgC))
    exact ae_of_all μ (fun x => by
      simpa only [H, probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (ae_of_all (ν n) (fun u => hgC (-u + x))))
  have hFlim : TendstoInMeasure μ F atTop f := by
    apply tendstoInMeasure_of_integral_norm_tendsto_zero μ F f hFi
    exact squeeze_zero (fun n => integral_nonneg (fun _ => norm_nonneg _)) hUerrF
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hHlim : TendstoInMeasure μ H atTop g := by
    apply tendstoInMeasure_of_integral_norm_tendsto_zero μ H g hHi
    exact squeeze_zero (fun n => integral_nonneg (fun _ => norm_nonneg _)) hUerrG
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨ns, hns, hnsF⟩ := hFlim.exists_seq_tendsto_ae
  obtain ⟨ms, hms, hmsH⟩ := (hHlim.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨fun n => U (ns (ms n)), fun n => ⟨hUopen _, hUzero _, hUpos _⟩, ?_, hmsH⟩
  exact hnsF.mono (fun x hx => hx.comp hms.tendsto_atTop)

end Erdos335.Loeb
