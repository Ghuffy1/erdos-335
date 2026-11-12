import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Differentiation on moving intermediate windows

Both endpoints may move by a bounded multiple of the window length.  The
approximation errors are divided by that length before passing to the limit.
-/

set_option autoImplicit false

open Filter Set Topology Asymptotics

namespace Erdos335.PeriodicRefinement

theorem normalized_derivative_remainder
    {F : ℝ → ℝ} {d x : ℝ} (hF : HasDerivAt F d x)
    (u h : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 x))
    (hscale : (fun n => u n - x) =O[atTop] h) :
    Tendsto (fun n => (F (u n) - F x - (u n - x) * d) / h n)
      atTop (𝓝 0) := by
  have hsmall := (hF.isLittleO.comp_tendsto hu).trans_isBigO hscale
  simpa only [Function.comp_def, smul_eq_mul] using hsmall.tendsto_div_nhds_zero

theorem moving_derivative_window_tendsto
    {F : ℝ → ℝ} {d x : ℝ} (hF : HasDerivAt F d x)
    (u v h : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 x))
    (hv : Tendsto v atTop (𝓝 x))
    (huscale : (fun n => u n - x) =O[atTop] h)
    (hvscale : (fun n => v n - x) =O[atTop] h)
    (hgap : ∀ᶠ n in atTop, v n - u n = h n)
    (hne : ∀ᶠ n in atTop, h n ≠ 0) :
    Tendsto (fun n => (F (v n) - F (u n)) / h n) atTop (𝓝 d) := by
  have hru := normalized_derivative_remainder hF u h hu huscale
  have hrv := normalized_derivative_remainder hF v h hv hvscale
  have hlim := (hrv.sub hru).add_const d
  simp only [sub_zero, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [hgap, hne] with n hgapn hnen
  rw [← sub_div]
  field_simp [hnen]
  rw [← hgapn]
  ring

theorem moving_approximate_derivative_window_tendsto
    {F : ℝ → ℝ} {d x : ℝ} (hF : HasDerivAt F d x)
    (G : ℕ → ℝ → ℝ) (u v h : ℕ → ℝ)
    (hu : Tendsto u atTop (𝓝 x)) (hv : Tendsto v atTop (𝓝 x))
    (huscale : (fun n => u n - x) =O[atTop] h)
    (hvscale : (fun n => v n - x) =O[atTop] h)
    (hgap : ∀ᶠ n in atTop, v n - u n = h n)
    (hne : ∀ᶠ n in atTop, h n ≠ 0)
    (huerror : Tendsto (fun n => (G n (u n) - F (u n)) / h n) atTop (𝓝 0))
    (hverror : Tendsto (fun n => (G n (v n) - F (v n)) / h n) atTop (𝓝 0)) :
    Tendsto (fun n => (G n (v n) - G n (u n)) / h n) atTop (𝓝 d) := by
  have hmain := moving_derivative_window_tendsto hF u v h hu hv huscale hvscale hgap hne
  have hlim := hmain.add (hverror.sub huerror)
  simp only [sub_zero, add_zero] at hlim
  apply hlim.congr
  intro n
  ring

end Erdos335.PeriodicRefinement
