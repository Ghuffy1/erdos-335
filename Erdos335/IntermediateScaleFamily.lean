import Erdos335.IntermediateLexicographicScales
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A family strictly inside an arbitrary growing scale gap
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos335.IntermediateScale

noncomputable def intermediateScale (lower upper : ℕ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  lower n * lexScale a b (Real.log (upper n / lower n))

theorem intermediateScale_div_lower_atTop (lower upper : ℕ → ℝ)
    (hlower : ∀ᶠ n in atTop, 0 < lower n)
    (hgap : Tendsto (fun n => upper n / lower n) atTop atTop)
    (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun n => intermediateScale lower upper a b n / lower n) atTop atTop := by
  apply ((lexScale_tendsto_atTop a b ha).comp (Real.tendsto_log_atTop.comp hgap)).congr'
  filter_upwards [hlower] with n hn
  simp only [Function.comp_def, intermediateScale]
  field_simp

theorem intermediateScale_div_upper_zero (lower upper : ℕ → ℝ)
    (hlower : ∀ᶠ n in atTop, 0 < lower n)
    (hgap : Tendsto (fun n => upper n / lower n) atTop atTop)
    (a b : ℝ) (ha : a < 1) :
    Tendsto (fun n => intermediateScale lower upper a b n / upper n) atTop (𝓝 0) := by
  apply ((lexScale_div_exp_tendsto_zero a b ha).comp
    (Real.tendsto_log_atTop.comp hgap)).congr'
  filter_upwards [hlower, hgap.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hg
  simp only [Function.comp_def, intermediateScale, Real.exp_log hg]
  field_simp

theorem intermediateScale_ratio_zero (lower upper : ℕ → ℝ)
    (hlower : ∀ᶠ n in atTop, 0 < lower n)
    (hgap : Tendsto (fun n => upper n / lower n) atTop atTop)
    (a b a' b' : ℝ) (horder : a < a' ∨ (a = a' ∧ b < b')) :
    Tendsto (fun n => intermediateScale lower upper a b n /
      intermediateScale lower upper a' b' n) atTop (𝓝 0) := by
  apply ((lexScale_ratio_tendsto_zero a b a' b' horder).comp
    (Real.tendsto_log_atTop.comp hgap)).congr'
  filter_upwards [hlower] with n hn
  simp only [Function.comp_def, intermediateScale]
  field_simp

theorem intermediateScale_atTop (lower upper : ℕ → ℝ)
    (hlower : ∀ᶠ n in atTop, 1 ≤ lower n)
    (hgap : Tendsto (fun n => upper n / lower n) atTop atTop)
    (a b : ℝ) (ha : 0 < a) :
    Tendsto (intermediateScale lower upper a b) atTop atTop := by
  have hbase := (lexScale_tendsto_atTop a b ha).comp (Real.tendsto_log_atTop.comp hgap)
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [hlower] with n hn
  exact le_mul_of_one_le_left (Real.exp_pos _).le hn

theorem floor_preserves_vanishing_ratio (f g : ℕ → ℝ)
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop)
    (hfg : Tendsto (fun n => f n / g n) atTop (𝓝 0)) :
    Tendsto (fun n => (⌊f n⌋₊ : ℝ) / (⌊g n⌋₊ : ℝ)) atTop (𝓝 0) := by
  have hfirst := (tendsto_nat_floor_div_atTop.comp hf)
  have hlast := (tendsto_nat_floor_div_atTop.comp hg).inv₀ (by norm_num)
  have hprod := (hfirst.mul hfg).mul hlast
  simp only [mul_zero, zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [hf.eventually (eventually_gt_atTop (0 : ℝ)),
    hg.eventually (eventually_gt_atTop (0 : ℝ))] with n hfn hgn
  dsimp only [Function.comp_def]
  field_simp

end Erdos335.IntermediateScale
