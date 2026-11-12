import Erdos335.CompactOverlapGap
import Erdos335.CirclePowerEscape

/-!
# Quantitative character widths for small summands

The estimate supplies the positive lower bound used in the second step
of Kneser's connected equality argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem exists_character_width_mass_bound
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (S : Set G) (hS : MeasurableSet S)
    (hperiod : ∀ t : G, t +ᵥ S =ᵐ[μ] S → t = 0)
    (χ : AddChar G Circle) (hχ : Continuous χ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ A B : Set G, (A + B ≤ᵐ[μ] S) →
      ∀ x ∈ B, ∀ y ∈ B,
        ε * |Complex.arg (χ (x - y) : ℂ)| ≤
          Real.pi * ((μ S).toReal - (μ A).toReal) := by
  let E : Set G := {t | (χ t : ℂ).re ≤ 0}
  have hEclosed : IsClosed E := isClosed_le
    (Complex.continuous_re.comp (continuous_subtype_val.comp hχ)) continuous_const
  have hzero : 0 ∉ E := by
    change ¬ (χ 0 : ℂ).re ≤ 0
    simp
  obtain ⟨ε, hε, hbound⟩ := exists_uniform_scaled_difference_mass_lower_bound μ S hS hperiod
    E hEclosed.isCompact hzero
  refine ⟨ε, hε, ?_⟩
  intro A B hsum x hx y hy
  have hbase : (μ A).toReal ≤ (μ S).toReal := by
    have h := haarOverlap_ge_of_sumset_ae_subset μ A B S hsum x x hx hx
    simpa only [sub_self, haarOverlap, zero_vadd, inter_self] using h
  have hnonneg : 0 ≤ (μ S).toReal - (μ A).toReal := sub_nonneg.mpr hbase
  by_cases hvalue : χ (x - y) = 1
  · rw [hvalue]
    simpa only [Circle.coe_one, Complex.arg_one, abs_zero, mul_zero] using
      mul_nonneg Real.pi_pos.le hnonneg
  · obtain ⟨n, _, hpower, hnwidth⟩ := exists_circle_power_nonpositive_real (χ (x - y)) hvalue
    have hnE : n • (x - y) ∈ E := by
      change (χ (n • (x - y)) : ℂ).re ≤ 0
      rw [AddChar.map_nsmul_eq_pow]
      exact hpower
    have hscaled := hbound A B hsum x hx y hy n hnE
    calc
      ε * |Complex.arg (χ (x - y) : ℂ)| ≤
          (n * ((μ S).toReal - (μ A).toReal)) * |Complex.arg (χ (x - y) : ℂ)| :=
        mul_le_mul_of_nonneg_right hscaled (abs_nonneg _)
      _ = ((n : ℝ) * |Complex.arg (χ (x - y) : ℂ)|) *
          ((μ S).toReal - (μ A).toReal) := by ring
      _ ≤ Real.pi * ((μ S).toReal - (μ A).toReal) :=
        mul_le_mul_of_nonneg_right hnwidth hnonneg

end Erdos335.Loeb
