import Erdos335.CompactOverlap

/-!
# Overlap loss as the positive part of an indicator difference
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem haarOverlap_neg_eq
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] (S : Set G) (t : G) :
    haarOverlap μ S (-t) = haarOverlap μ S t := by
  have hmeasure (E : Set G) : μ (t +ᵥ E) = μ E := by
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have hset : t +ᵥ (S ∩ (-t +ᵥ S)) = (t +ᵥ S) ∩ S := by
    rw [vadd_set_inter, vadd_vadd, add_neg_cancel, zero_vadd]
  change (μ (S ∩ (-t +ᵥ S))).toReal = (μ (S ∩ (t +ᵥ S))).toReal
  rw [← hmeasure (S ∩ (-t +ᵥ S)), hset, inter_comm]

theorem haarOverlap_loss_eq_positive_part_integral
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (S : Set G) (hS : MeasurableSet S) (t : G) :
    (μ S).toReal - haarOverlap μ S t =
      ∫ x, max (S.indicator (fun _ => (1 : ℝ)) x -
        S.indicator (fun _ => (1 : ℝ)) (t + x)) 0 ∂μ := by
  let T : Set G := (fun x => t + x) ⁻¹' S
  let D : Set G := S \ T
  have hT : MeasurableSet T := hS.preimage (measurable_const.add measurable_id)
  have hD : MeasurableSet D := hS.diff hT
  have hpoint : (fun x => max (S.indicator (fun _ => (1 : ℝ)) x -
      S.indicator (fun _ => (1 : ℝ)) (t + x)) 0) = D.indicator (fun _ => 1) := by
    funext x
    by_cases hx : x ∈ S <;> by_cases ht : t + x ∈ S <;> simp [D, T, hx, ht]
  have hIntegral : (∫ x, D.indicator (fun _ => (1 : ℝ)) x ∂μ) = (μ D).toReal := by
    simpa only [smul_eq_mul, mul_one, measureReal_def] using
      integral_indicator_const (1 : ℝ) hD (μ := μ)
  rw [hpoint, hIntegral]
  have hpartition := congrArg ENNReal.toReal (measure_inter_add_sdiff (μ := μ) S hT)
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hpartition
  have hinter : (μ (S ∩ T)).toReal = haarOverlap μ S (-t) := by
    change (μ (S ∩ T)).toReal = (μ (S ∩ (-t +ᵥ S))).toReal
    rw [vadd_set_eq_neg_preimage, neg_neg]
  rw [hinter, haarOverlap_neg_eq μ S t] at hpartition
  change (μ S).toReal - haarOverlap μ S t = (μ (S \ T)).toReal
  linarith

end Erdos335.Loeb
