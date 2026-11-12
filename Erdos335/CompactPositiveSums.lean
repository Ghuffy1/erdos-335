import Erdos335.LoebIndicators
import Mathlib.MeasureTheory.Group.Integral

/-!
# Positive convolution from overlapping local pieces

The overlap argument in Griesmer's compact sumset reduction is stated with
literal preimages. Two subsets of a finite-measure neighborhood whose
measures add to more than the neighborhood measure have positive overlap.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem measure_inter_pos_of_sum_gt
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (U S T : Set X)
    (hS : S ⊆ U) (hT : T ⊆ U) (hTm : MeasurableSet T)
    (hsum : μ U < μ S + μ T) : 0 < μ (S ∩ T) := by
  by_contra h
  have hzero : μ (S ∩ T) = 0 := le_antisymm (not_lt.mp h) zero_le
  have heq := measure_union_add_inter (μ := μ) S hTm
  rw [hzero, add_zero] at heq
  have hle : μ S + μ T ≤ μ U := heq ▸ measure_mono (union_subset hS hT)
  exact (not_lt_of_ge hle) hsum

theorem indicator_convolution_eq_measure_inter
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B) (x : G) :
    (∫ t, A.indicator (fun _ => (1 : ℝ)) t * B.indicator (fun _ => (1 : ℝ)) (x - t) ∂μ) =
      (μ (A ∩ (fun t => x - t) ⁻¹' B)).toReal := by
  classical
  have hset : MeasurableSet (A ∩ (fun t => x - t) ⁻¹' B) :=
    hA.inter (hB.preimage (measurable_const.sub measurable_id))
  have hfun : (fun t => A.indicator (fun _ => (1 : ℝ)) t * B.indicator (fun _ => (1 : ℝ)) (x - t)) =
      (A ∩ (fun t => x - t) ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases ha : t ∈ A <;> by_cases hb : x - t ∈ B <;> simp [ha, hb]
  rw [hfun, integral_indicator hset]
  simp [measureReal_def]

theorem positive_indicator_convolution_of_local_overlap
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (U A B : Set G) (hU : MeasurableSet U) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (x y : G)
    (hsum : μ U < μ (U ∩ (fun t => x + t) ⁻¹' A) + μ (U ∩ (fun t => y - t) ⁻¹' B)) :
    0 < ∫ t, A.indicator (fun _ => (1 : ℝ)) t *
      B.indicator (fun _ => (1 : ℝ)) (x + y - t) ∂μ := by
  classical
  let S := U ∩ (fun t => x + t) ⁻¹' A
  let T := U ∩ (fun t => y - t) ⁻¹' B
  let W := (fun t => x + t) ⁻¹' A ∩ (fun t => y - t) ⁻¹' B
  have hT : MeasurableSet T := hU.inter (hB.preimage (measurable_const.sub measurable_id))
  have hover : 0 < μ (S ∩ T) :=
    measure_inter_pos_of_sum_gt μ U S T inter_subset_left inter_subset_left hT hsum
  have hW : MeasurableSet W :=
    (hA.preimage (measurable_const.add measurable_id)).inter
      (hB.preimage (measurable_const.sub measurable_id))
  have hWpos : 0 < μ W := hover.trans_le (measure_mono (by
    intro t ht
    exact ⟨ht.1.2, ht.2.2⟩))
  have hfun : (fun t => A.indicator (fun _ => (1 : ℝ)) (x + t) *
      B.indicator (fun _ => (1 : ℝ)) (y - t)) = W.indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases ha : x + t ∈ A <;> by_cases hb : y - t ∈ B <;> simp [W, ha, hb]
  have hint : 0 < ∫ t, A.indicator (fun _ => (1 : ℝ)) (x + t) *
      B.indicator (fun _ => (1 : ℝ)) (y - t) ∂μ := by
    rw [hfun, integral_indicator hW]
    simpa [measureReal_def] using ENNReal.toReal_pos hWpos.ne' (measure_ne_top μ W)
  have hshift := integral_add_left_eq_self (μ := μ)
    (fun t => A.indicator (fun _ => (1 : ℝ)) t *
      B.indicator (fun _ => (1 : ℝ)) (x + y - t)) x
  have heq (t : G) : x + y - (x + t) = y - t := by abel
  simp only [heq] at hshift
  exact hshift ▸ hint

end Erdos335.Loeb
