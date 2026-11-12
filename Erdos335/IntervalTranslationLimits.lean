import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# Endpoint derivatives and small translation bounds
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory

namespace Erdos335.Loeb

theorem derivative_alternating_sum_le_of_varying_increment_bounds
    (F : ℝ → ℝ) (a b c d α β γ δ M : ℝ)
    (ha : HasDerivAt F α a) (hb : HasDerivAt F β b)
    (hc : HasDerivAt F γ c) (hd : HasDerivAt F δ d)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (hpos : ∀ n, 0 < t n)
    (m : ℕ → ℝ) (hm : Tendsto m atTop (𝓝 M))
    (hbound : ∀ n,
      (F (a + t n) - F a) - (F (b + t n) - F b) +
        (F (c + t n) - F c) - (F (d + t n) - F d) ≤ m n * t n) :
    α - β + γ - δ ≤ M := by
  have hright : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hpos⟩
  have hlimit := (((ha.tendsto_slope_zero_right.comp hright).sub
    (hb.tendsto_slope_zero_right.comp hright)).add
    (hc.tendsto_slope_zero_right.comp hright)).sub (hd.tendsto_slope_zero_right.comp hright)
  have heventual : ∀ᶠ n in atTop,
      (t n)⁻¹ * (F (a + t n) - F a) - (t n)⁻¹ * (F (b + t n) - F b) +
        (t n)⁻¹ * (F (c + t n) - F c) - (t n)⁻¹ * (F (d + t n) - F d) ≤ m n := by
    apply Eventually.of_forall
    intro n
    have hdivide := (div_le_iff₀ (hpos n)).mpr (hbound n)
    convert hdivide using 1 <;> ring
  apply le_of_tendsto_of_tendsto hlimit hm
  filter_upwards [heventual] with n hn
  simpa only [Function.comp_apply, smul_eq_mul] using hn

theorem derivative_alternating_sum_le_of_increment_bounds
    (F : ℝ → ℝ) (a b c d α β γ δ M : ℝ)
    (ha : HasDerivAt F α a) (hb : HasDerivAt F β b)
    (hc : HasDerivAt F γ c) (hd : HasDerivAt F δ d)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (hpos : ∀ n, 0 < t n)
    (hbound : ∀ n,
      (F (a + t n) - F a) - (F (b + t n) - F b) +
        (F (c + t n) - F c) - (F (d + t n) - F d) ≤ M * t n) :
    α - β + γ - δ ≤ M :=
  derivative_alternating_sum_le_of_varying_increment_bounds F a b c d α β γ δ M
    ha hb hc hd t ht hpos (fun _ => M) tendsto_const_nhds hbound

theorem interval_integral_translation_endpoints
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (a b t : ℝ) :
    (∫ x in a..b, f x - f (x + t)) =
      ((∫ x in 0..a + t, f x) - ∫ x in 0..a, f x) -
        ((∫ x in 0..b + t, f x) - ∫ x in 0..b, f x) := by
  have hi (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hshift : IntervalIntegrable (fun x => f (x + t)) volume a b :=
    (IntervalIntegrable.comp_add_right_iff (f := f) (a := a) (b := b) (c := t)).mpr
      (hi (a + t) (b + t))
  rw [intervalIntegral.integral_sub (hi a b) hshift, intervalIntegral.integral_comp_add_right]
  rw [← intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a),
    ← intervalIntegral.integral_interval_sub_left (hi 0 (b + t)) (hi 0 (a + t))]
  ring

theorem derivative_alternating_sum_le_of_translation_integrals
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (a b c d α β γ δ M : ℝ)
    (ha : HasDerivAt (fun y => ∫ x in 0..y, f x) α a)
    (hb : HasDerivAt (fun y => ∫ x in 0..y, f x) β b)
    (hc : HasDerivAt (fun y => ∫ x in 0..y, f x) γ c)
    (hd : HasDerivAt (fun y => ∫ x in 0..y, f x) δ d)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (hpos : ∀ n, 0 < t n)
    (hbound : ∀ n, (∫ x in a..b, f x - f (x + t n)) +
      (∫ x in c..d, f x - f (x + t n)) ≤ M * t n) :
    α - β + γ - δ ≤ M := by
  apply derivative_alternating_sum_le_of_increment_bounds
    (fun y => ∫ x in 0..y, f x) a b c d α β γ δ M ha hb hc hd t ht hpos
  intro n
  have h := hbound n
  rw [interval_integral_translation_endpoints f hf a b,
    interval_integral_translation_endpoints f hf c d] at h
  linarith

theorem derivative_alternating_sum_le_of_varying_translation_integrals
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (a b c d α β γ δ M : ℝ)
    (ha : HasDerivAt (fun y => ∫ x in 0..y, f x) α a)
    (hb : HasDerivAt (fun y => ∫ x in 0..y, f x) β b)
    (hc : HasDerivAt (fun y => ∫ x in 0..y, f x) γ c)
    (hd : HasDerivAt (fun y => ∫ x in 0..y, f x) δ d)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (hpos : ∀ n, 0 < t n)
    (m : ℕ → ℝ) (hm : Tendsto m atTop (𝓝 M))
    (hbound : ∀ n, (∫ x in a..b, f x - f (x + t n)) +
      (∫ x in c..d, f x - f (x + t n)) ≤ m n * t n) :
    α - β + γ - δ ≤ M := by
  apply derivative_alternating_sum_le_of_varying_increment_bounds
    (fun y => ∫ x in 0..y, f x) a b c d α β γ δ M ha hb hc hd t ht hpos m hm
  intro n
  have h := hbound n
  rw [interval_integral_translation_endpoints f hf a b,
    interval_integral_translation_endpoints f hf c d] at h
  linarith

end Erdos335.Loeb
