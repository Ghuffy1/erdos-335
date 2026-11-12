import Erdos335.PeriodicRefinementCumulative
import Erdos335.DensityMacroscopicIntervals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Recovering density data from cumulative limits
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped NNReal

noncomputable section

namespace Erdos335.PeriodicRefinement

theorem cumulative_limit_of_density
    (S : Set ℕ) (ρ : ℝ) (hS : HasDensity S ρ)
    (G : ℝ → ℝ) (hG : LipschitzWith 1 G)
    (hgrid : ∀ k : ℕ, G k = prefixCount S k)
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNtop : Tendsto N atTop atTop)
    (t y : ℝ) (ht : 0 ≤ t)
    (hlim : Tendsto (fun n => G (t * N n) / N n) atTop (𝓝 y)) :
    y = ρ * t := by
  have hraw := hS.prefixCount_floor_real_tendsto (fun n => (N n : ℝ))
    (tendsto_natCast_atTop_atTop.comp hNtop) t ht
  have herror : Tendsto (fun n =>
      |G (t * N n) / N n - (prefixCount S (Nat.floor (t * N n)) : ℝ) / N n|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _)
      (fun n => rescaled_prefix_count_error S G hG hgrid (N n) (hN n) t ht)
    exact (tendsto_const_div_atTop_nhds_zero_nat 1).comp hNtop
  have hdiff : Tendsto (fun n =>
      G (t * N n) / N n - (prefixCount S (Nat.floor (t * N n)) : ℝ) / N n)
      atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero).mpr herror
  have htarget := hraw.add hdiff
  simp only [add_zero] at htarget
  have htarget' : Tendsto (fun n => G (t * N n) / N n) atTop (𝓝 (ρ * t)) := by
    apply htarget.congr
    intro n
    ring
  exact tendsto_nhds_unique hlim htarget'

theorem cumulative_value_of_ae_derivative
    (F : ℝ → ℝ) (K : ℝ≥0) (hF : LipschitzWith K F) (hzero : F 0 = 0)
    (c t : ℝ) (ht : 0 ≤ t)
    (hd : ∀ᵐ x ∂volume, 0 < x → deriv F x = c) :
    F t = t * c := by
  have hFTC := (hF.lipschitzOnWith (s := Set.uIcc 0 t)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hint : (∫ x : ℝ in (0 : ℝ)..t, deriv F x) = ∫ _x : ℝ in (0 : ℝ)..t, c := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with x hx hxt
    rw [Set.uIoc_of_le ht] at hxt
    exact hx hxt.1
  rw [hint, intervalIntegral.integral_const, hzero, sub_zero] at hFTC
  simpa only [sub_zero, smul_eq_mul] using hFTC.symm

end Erdos335.PeriodicRefinement

end
