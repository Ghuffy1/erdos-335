import Erdos335.CompactDysonTransform
import Erdos335.CompactLocalization
import Erdos335.CompactConvolutionContinuity
import Erdos335.CompactPositiveSums

/-!
# Continuous overlap and essential periods
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]

def haarOverlap (μ : Measure G) (S : Set G) (z : G) : ℝ :=
  (μ (S ∩ (z +ᵥ S))).toReal

theorem continuous_haarOverlap
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (S : Set G) (hS : MeasurableSet S) : Continuous (haarOverlap μ S) := by
  classical
  have hneg : MeasurableSet (-S) := hS.neg
  have hc := continuous_bounded_real_convolution μ
    (S.indicator fun _ => (1 : ℝ)) ((-S).indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hS) (measurable_const.indicator hneg)
    (fun x => by by_cases hx : x ∈ S <;> simp [hx])
    (fun x => by by_cases hx : x ∈ -S <;> simp [hx])
  have hset (z : G) : S ∩ (fun t => z - t) ⁻¹' (-S) = S ∩ (z +ᵥ S) := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      change -(z - x) ∈ S at hy
      refine ⟨hx, x - z, ?_, ?_⟩
      · simpa only [neg_sub] using hy
      · change z + (x - z) = x
        abel
    · rintro ⟨hx, y, hy, hxy⟩
      refine ⟨hx, ?_⟩
      change z + y = x at hxy
      change -(z - x) ∈ S
      rw [← hxy]
      simpa only [sub_add_cancel_left, neg_neg] using hy
  convert hc using 1
  funext z
  rw [indicator_convolution_eq_measure_inter μ S (-S) hS hneg, hset]
  rfl

theorem haarOverlap_eq_full_iff
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (S : Set G) (hS : MeasurableSet S) (z : G) :
    haarOverlap μ S z = (μ S).toReal ↔ z +ᵥ S =ᵐ[μ] S := by
  have hzm : MeasurableSet (z +ᵥ S) := by
    rw [vadd_set_eq_neg_preimage]
    exact hS.preimage (measurable_const.add measurable_id)
  have hmass : μ (z +ᵥ S) = μ S := by
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  constructor
  · intro h
    have hinter : μ (S ∩ (z +ᵥ S)) = μ S := by
      have heq := congrArg ENNReal.ofReal h
      simpa only [haarOverlap, ENNReal.ofReal_toReal (measure_ne_top μ _)] using heq
    have hleftSet : S \ (z +ᵥ S) = S \ (S ∩ (z +ᵥ S)) := by
      ext x
      simp only [Set.mem_sdiff, mem_inter_iff]
      tauto
    have hrightSet : (z +ᵥ S) \ S = (z +ᵥ S) \ ((z +ᵥ S) ∩ S) := by
      ext x
      simp only [Set.mem_sdiff, mem_inter_iff]
      tauto
    have hleft : μ (S \ (z +ᵥ S)) = 0 := by
      rw [hleftSet, measure_sdiff inter_subset_left
        (hS.inter hzm).nullMeasurableSet (measure_ne_top μ _), hinter, tsub_self]
    have hright : μ ((z +ᵥ S) \ S) = 0 := by
      rw [hrightSet, measure_sdiff inter_subset_left
        (hzm.inter hS).nullMeasurableSet (measure_ne_top μ _), inter_comm, hinter, hmass, tsub_self]
    exact (ae_le_set.mpr hright).antisymm (ae_le_set.mpr hleft)
  · intro h
    have hinter : S ∩ (z +ᵥ S) =ᵐ[μ] S := by
      filter_upwards [h] with x hx
      change (x ∈ S ∧ x ∈ z +ᵥ S) = (x ∈ S)
      rw [hx]
      exact and_self _
    exact congrArg ENNReal.toReal (measure_congr hinter)

theorem haarOverlap_strict_maximum
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (S : Set G) (hS : MeasurableSet S)
    (hperiod : ∀ z : G, z +ᵥ S =ᵐ[μ] S → z = 0) :
    ∀ z : G, z ≠ 0 → haarOverlap μ S z < haarOverlap μ S 0 := by
  intro z hz
  have hle : haarOverlap μ S z ≤ (μ S).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono inter_subset_left)
  have hne : haarOverlap μ S z ≠ (μ S).toReal := by
    intro heq
    exact hz (hperiod z ((haarOverlap_eq_full_iff μ S hS z).mp heq))
  have hlt := lt_of_le_of_ne hle hne
  simpa only [haarOverlap, zero_vadd, inter_self] using hlt

end Erdos335.Loeb

end
