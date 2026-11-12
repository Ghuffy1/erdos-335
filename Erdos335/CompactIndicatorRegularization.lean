import Erdos335.HaarApproxSequence
import Erdos335.CompactPositiveSums
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Full-measure representatives with positive convolution on every sum

This proves the indicator case of the compact sumset regularization used
by Griesmer. The common local averages converge almost everywhere. At two
points in their original sets, their local densities eventually exceed
one half, and the overlap estimate gives positive convolution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

namespace Erdos335.Loeb

theorem local_indicator_average_eq
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsFiniteMeasure μ] (U A : Set G) (hA : MeasurableSet A)
    (T : G → G) (hT : Measurable T) (x : G) :
    (∫ u, A.indicator (fun _ => (1 : ℝ)) (T u + x) ∂((μ U)⁻¹ • μ.restrict U)) =
      (μ (U ∩ (fun u => T u + x) ⁻¹' A)).toReal / (μ U).toReal := by
  have hP : MeasurableSet ((fun u => T u + x) ⁻¹' A) :=
    hA.preimage (hT.add measurable_const)
  have heq : (fun u => A.indicator (fun _ => (1 : ℝ)) (T u + x)) =
      ((fun u => T u + x) ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext u
    by_cases h : T u + x ∈ A <;> simp [h]
  rw [heq, integral_indicator hP]
  simp [measureReal_def, Measure.smul_apply, Measure.restrict_apply hP,
    ENNReal.toReal_mul, ENNReal.toReal_inv, inter_comm, div_eq_mul_inv, mul_comm]

theorem positive_indicator_convolution_of_local_limits
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (U : ℕ → Set G) (hUm : ∀ n, MeasurableSet (U n)) (hUp : ∀ n, 0 < μ (U n))
    (x y : G)
    (hx : Tendsto (fun n => ∫ u, A.indicator (fun _ => (1 : ℝ)) (u + x)
      ∂((μ (U n))⁻¹ • μ.restrict (U n))) atTop (𝓝 1))
    (hy : Tendsto (fun n => ∫ u, B.indicator (fun _ => (1 : ℝ)) (-u + y)
      ∂((μ (U n))⁻¹ • μ.restrict (U n))) atTop (𝓝 1)) :
    0 < ∫ t, A.indicator (fun _ => (1 : ℝ)) t *
      B.indicator (fun _ => (1 : ℝ)) (x + y - t) ∂μ := by
  obtain ⟨n, hnA, hnB⟩ := ((hx.eventually (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num))).and
    (hy.eventually (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num)))).exists
  have hlocA := local_indicator_average_eq μ (U n) A hA id measurable_id x
  simp only [id_eq] at hlocA
  rw [hlocA] at hnA
  rw [local_indicator_average_eq μ (U n) B hB (fun u => -u) measurable_neg y] at hnB
  have hUpR : 0 < (μ (U n)).toReal := ENNReal.toReal_pos (hUp n).ne' (measure_ne_top μ _)
  have hnAR := (lt_div_iff₀ hUpR).mp hnA
  have hnBR := (lt_div_iff₀ hUpR).mp hnB
  apply positive_indicator_convolution_of_local_overlap μ (U n) A B (hUm n) hA hB x y
  apply (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by finiteness)).mp
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  simp only [add_comm] at hnAR hnBR
  simp only [sub_eq_add_neg]
  nlinarith

theorem exists_full_measure_indicator_representatives
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsOpenPosMeasure]
    (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∃ A' B' : Set G,
      MeasurableSet A' ∧ MeasurableSet B' ∧ A' ⊆ A ∧ B' ⊆ B ∧
      μ A' = μ A ∧ μ B' = μ B ∧
      ∀ x ∈ A', ∀ y ∈ B',
        0 < ∫ t, A.indicator (fun _ => (1 : ℝ)) t *
          B.indicator (fun _ => (1 : ℝ)) (x + y - t) ∂μ := by
  have hf : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
  have hg : Measurable (B.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hB
  obtain ⟨U, hU, hconvA, hconvB⟩ := exists_common_local_average_ae μ
    (A.indicator (fun _ => (1 : ℝ))) (B.indicator (fun _ => (1 : ℝ))) hf hg
    (fun x => by simpa only [Real.norm_eq_abs] using indicator_one_abs_le A x)
    (fun x => by simpa only [Real.norm_eq_abs] using indicator_one_abs_le B x)
  let F (n : ℕ) (x : G) := ∫ u, A.indicator (fun _ => (1 : ℝ)) (u + x)
    ∂((μ (U n))⁻¹ • μ.restrict (U n))
  let H (n : ℕ) (x : G) := ∫ u, B.indicator (fun _ => (1 : ℝ)) (-u + x)
    ∂((μ (U n))⁻¹ • μ.restrict (U n))
  have hFm (n : ℕ) : Measurable (F n) := by
    letI := isProbabilityMeasure_normalized_restrict μ (U n) (hU n).2.2
    exact (show StronglyMeasurable (fun p : G × G => A.indicator (fun _ => (1 : ℝ)) (p.2 + p.1))
      from (hf.comp (measurable_snd.add measurable_fst)).stronglyMeasurable).integral_prod_right'.measurable
  have hHm (n : ℕ) : Measurable (H n) := by
    letI := isProbabilityMeasure_normalized_restrict μ (U n) (hU n).2.2
    exact (show StronglyMeasurable (fun p : G × G => B.indicator (fun _ => (1 : ℝ)) (-p.2 + p.1))
      from (hg.comp (measurable_snd.neg.add measurable_fst)).stronglyMeasurable).integral_prod_right'.measurable
  let A' := A ∩ {x | Tendsto (fun n => F n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x))}
  let B' := B ∩ {x | Tendsto (fun n => H n x) atTop (𝓝 (B.indicator (fun _ => (1 : ℝ)) x))}
  have hAeq : A' =ᵐ[μ] A := by
    filter_upwards [hconvA] with x hx
    change (x ∈ A ∧ Tendsto (fun n => F n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x))) = (x ∈ A)
    have hx' : Tendsto (fun n => F n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x)) := hx
    simp only [hx', and_true]
  have hBeq : B' =ᵐ[μ] B := by
    filter_upwards [hconvB] with x hx
    change (x ∈ B ∧ Tendsto (fun n => H n x) atTop (𝓝 (B.indicator (fun _ => (1 : ℝ)) x))) = (x ∈ B)
    have hx' : Tendsto (fun n => H n x) atTop (𝓝 (B.indicator (fun _ => (1 : ℝ)) x)) := hx
    simp only [hx', and_true]
  refine ⟨A', B', hA.inter (measurableSet_tendsto_fun hFm hf),
    hB.inter (measurableSet_tendsto_fun hHm hg), inter_subset_left,
    inter_subset_left, measure_congr hAeq, measure_congr hBeq, ?_⟩
  intro x hx y hy
  apply positive_indicator_convolution_of_local_limits μ A B hA hB U
    (fun n => (hU n).1.measurableSet) (fun n => (hU n).2.2) x y
  · have hlim : Tendsto (fun n => F n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x)) := hx.2
    rw [Set.indicator_of_mem hx.1] at hlim
    exact hlim
  · have hlim : Tendsto (fun n => H n y) atTop (𝓝 (B.indicator (fun _ => (1 : ℝ)) y)) := hy.2
    rw [Set.indicator_of_mem hy.1] at hlim
    exact hlim

end Erdos335.Loeb
