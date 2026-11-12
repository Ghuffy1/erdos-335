import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Scales ordered by two real parameters

Writing `t = log(upper/lower)`, the scale multiplier is
`exp(a*t + b*log(t))`. Every fixed `a` in `(0,1)` gives an intermediate
scale, and the pair `(a,b)` orders these multipliers lexicographically.
The secondary scale depends on the ratio of the two supplied bounds.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos335.IntermediateScale

noncomputable def lexScale (a b t : ℝ) : ℝ :=
  Real.exp (a * t + b * Real.log t)

theorem linear_log_tendsto_atTop (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => a * t + b * Real.log t) atTop atTop := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hcoef : Tendsto (fun t : ℝ => a + b * (Real.log t / t)) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds.add (hlog.const_mul b))
  apply (hcoef.pos_mul_atTop ha tendsto_id).congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  dsimp
  field_simp

theorem linear_log_tendsto_atBot (a b : ℝ) (ha : a < 0) :
    Tendsto (fun t : ℝ => a * t + b * Real.log t) atTop atBot := by
  have h := tendsto_neg_atTop_atBot.comp
    (linear_log_tendsto_atTop (-a) (-b) (by linarith))
  simpa only [Function.comp_def, neg_add_rev, neg_mul, neg_neg, add_comm] using h

theorem lexScale_ratio_tendsto_zero (a b a' b' : ℝ)
    (horder : a < a' ∨ (a = a' ∧ b < b')) :
    Tendsto (fun t : ℝ => lexScale a b t / lexScale a' b' t) atTop (𝓝 0) := by
  have hbot : Tendsto (fun t : ℝ => (a - a') * t + (b - b') * Real.log t)
      atTop atBot := by
    rcases horder with ha | ⟨rfl, hb⟩
    · exact linear_log_tendsto_atBot _ _ (sub_neg.mpr ha)
    · simpa using Real.tendsto_log_atTop.const_mul_atTop_of_neg (sub_neg.mpr hb)
  apply (Real.tendsto_exp_atBot.comp hbot).congr
  intro t
  rw [lexScale, lexScale, ← Real.exp_sub]
  exact congrArg Real.exp (by ring)

theorem lexScale_tendsto_atTop (a b : ℝ) (ha : 0 < a) :
    Tendsto (lexScale a b) atTop atTop :=
  Real.tendsto_exp_atTop.comp (linear_log_tendsto_atTop a b ha)

theorem lexScale_div_exp_tendsto_zero (a b : ℝ) (ha : a < 1) :
    Tendsto (fun t : ℝ => lexScale a b t / Real.exp t) atTop (𝓝 0) := by
  simpa only [lexScale, zero_mul, add_zero, one_mul] using
    lexScale_ratio_tendsto_zero a b 1 0 (Or.inl ha)

end Erdos335.IntermediateScale
