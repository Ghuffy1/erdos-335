import Erdos335.HaarTranslation
import Erdos335.ProbabilityAverage
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Local probability averages on a compact group

Translation continuity and the integral norm inequality provide one
neighborhood average that approximates finitely many bounded functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

theorem isProbabilityMeasure_normalized_restrict
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]
    (U : Set G) (hU : 0 < μ U) :
    IsProbabilityMeasure ((μ U)⁻¹ • μ.restrict U) := by
  constructor
  simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hU.ne' (measure_ne_top μ U)

theorem integral_norm_translate_average_sub_le
    {G U : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableSpace U]
    (μ : Measure G) [IsFiniteMeasure μ] (ν : Measure U) [IsProbabilityMeasure ν]
    (T : U → G) (hT : Measurable T) (f : G → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (ε : ℝ)
    (hε : ∀ᵐ u ∂ν, (∫ x, ‖f (T u + x) - f x‖ ∂μ) ≤ ε) :
    (∫ x, ‖(∫ u, f (T u + x) ∂ν) - f x‖ ∂μ) ≤ ε := by
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all μ hC)
  have hF : Integrable (fun p : G × U => f (T p.2 + p.1)) (μ.prod ν) :=
    Integrable.of_bound (hf.comp ((hT.comp measurable_snd).add measurable_fst)).aestronglyMeasurable
      C (ae_of_all _ (fun p => hC _))
  calc
    _ ≤ ∫ u, ∫ x, ‖f (T u + x) - f x‖ ∂μ ∂ν :=
      integral_norm_probability_average_sub_le μ ν (fun x u => f (T u + x)) f hF hfi
    _ ≤ ∫ _u, ε ∂ν := by
      apply integral_mono_ae _ (integrable_const ε) hε
      exact (hF.sub (hfi.comp_fst ν)).integral_norm_prod_right
    _ = ε := by simp

theorem exists_common_local_average
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsOpenPosMeasure]
    (f g : G → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C : ℝ) (hfC : ∀ x, ‖f x‖ ≤ C) (hgC : ∀ x, ‖g x‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set G, IsOpen U ∧ 0 ∈ U ∧ 0 < μ U ∧
      (∫ x, ‖(∫ u, f (u + x) ∂((μ U)⁻¹ • μ.restrict U)) - f x‖ ∂μ) ≤ ε ∧
      (∫ x, ‖(∫ u, g (-u + x) ∂((μ U)⁻¹ • μ.restrict U)) - g x‖ ∂μ) ≤ ε := by
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all μ hfC)
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all μ hgC)
  have hflim := tendsto_integral_norm_add_sub_zero μ f hfi
  have hglim := (tendsto_integral_norm_add_sub_zero μ g hgi).comp
    (show Tendsto (fun u : G => -u) (𝓝 0) (𝓝 0) from by simpa using continuous_neg.tendsto (0 : G))
  have hsmall : ∀ᶠ u in 𝓝 (0 : G),
      (∫ x, ‖f (u + x) - f x‖ ∂μ) < ε ∧
      (∫ x, ‖g (-u + x) - g x‖ ∂μ) < ε :=
    (hflim.eventually (eventually_lt_nhds hε)).and (hglim.eventually (eventually_lt_nhds hε))
  obtain ⟨U, hUsub, hUopen, hUzero⟩ := mem_nhds_iff.mp hsmall
  have hUpos : 0 < μ U := hUopen.measure_pos μ ⟨0, hUzero⟩
  let ν := (μ U)⁻¹ • μ.restrict U
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_normalized_restrict μ U hUpos
  have hUae : ∀ᵐ u ∂ν, u ∈ U := Measure.ae_smul_measure (ae_restrict_mem hUopen.measurableSet) _
  refine ⟨U, hUopen, hUzero, hUpos, ?_, ?_⟩
  · apply integral_norm_translate_average_sub_le μ ν id measurable_id f hf C hfC ε
    exact hUae.mono (fun u hu => (hUsub hu).1.le)
  · apply integral_norm_translate_average_sub_le μ ν (fun u => -u) measurable_neg g hg C hgC ε
    exact hUae.mono (fun u hu => (hUsub hu).2.le)

end Erdos335.Loeb
