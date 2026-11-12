import Erdos335.CompactOverlap
import Mathlib.Analysis.Convolution

/-!
# Intersection profiles for the compact inverse theorem

The translate-intersection profile is continuous, its integral is the
product of the input measures, and its positive support lies in the
literal difference set.
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

def compactIntersectionProfile (μ : Measure G) (A B : Set G) (e : G) : ℝ :=
  (μ (A ∩ (e +ᵥ B))).toReal

omit [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [BorelSpace G] in
theorem indicator_convolution_eq_intersectionProfile
    (μ : Measure G) (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B) (e : G) :
    (∫ t, A.indicator (fun _ => (1 : ℝ)) t * (-B).indicator (fun _ => (1 : ℝ)) (e - t) ∂μ) =
      compactIntersectionProfile μ A B e := by
  rw [indicator_convolution_eq_measure_inter μ A (-B) hA hB.neg]
  have heq : A ∩ (fun t => e - t) ⁻¹' (-B) = A ∩ (e +ᵥ B) := by
    ext x
    constructor
    · rintro ⟨hx, hb⟩
      change -(e - x) ∈ B at hb
      exact ⟨hx, x - e, by simpa only [neg_sub] using hb, by change e + (x - e) = x; abel⟩
    · rintro ⟨hx, b, hb, heq⟩
      refine ⟨hx, ?_⟩
      change e + b = x at heq
      change -(e - x) ∈ B
      rw [← heq]
      simpa only [sub_add_cancel_left, neg_neg] using hb
  rw [heq]
  rfl

theorem continuous_compactIntersectionProfile
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Continuous (compactIntersectionProfile μ A B) := by
  classical
  have hc := continuous_bounded_real_convolution μ
    (A.indicator fun _ => (1 : ℝ)) ((-B).indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hA) (measurable_const.indicator hB.neg)
    (fun x => by by_cases hx : x ∈ A <;> simp [hx])
    (fun x => by by_cases hx : x ∈ -B <;> simp [hx])
  convert hc using 1
  funext e
  exact (indicator_convolution_eq_intersectionProfile μ A B hA hB e).symm

theorem integral_compactIntersectionProfile
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ e, compactIntersectionProfile μ A B e ∂μ) = (μ A).toReal * (μ B).toReal := by
  calc
    (∫ e, compactIntersectionProfile μ A B e ∂μ) =
        ∫ e, ∫ t, A.indicator (fun _ => (1 : ℝ)) t * (-B).indicator (fun _ => (1 : ℝ)) (e - t) ∂μ ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ fun e => (indicator_convolution_eq_intersectionProfile μ A B hA hB e).symm
    _ = (∫ t, A.indicator (fun _ => (1 : ℝ)) t ∂μ) *
        (∫ t, (-B).indicator (fun _ => (1 : ℝ)) t ∂μ) :=
      integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
        ((integrable_const _).indicator hA) ((integrable_const _).indicator hB.neg)
    _ = (μ A).toReal * (μ B).toReal := by
      rw [integral_indicator hA, integral_indicator hB.neg]
      simp [measureReal_def]

theorem compactIntersectionProfile_positive_support_subset
    (μ : Measure G) (A B : Set G) :
    {e | 0 < compactIntersectionProfile μ A B e} ⊆ A + (-B) := by
  intro e he
  change 0 < compactIntersectionProfile μ A B e at he
  have hne : μ (A ∩ (e +ᵥ B)) ≠ 0 := by
    intro hzero
    simpa only [compactIntersectionProfile, hzero, ENNReal.toReal_zero, lt_self_iff_false] using he
  obtain ⟨a, ha, b, hb, heq⟩ := nonempty_of_measure_ne_zero hne
  refine ⟨a, ha, -b, ?_, ?_⟩
  · change -(-b) ∈ B
    simpa only [neg_neg] using hb
  · change e + b = a at heq
    rw [← heq]
    abel

end Erdos335.Loeb

end
