import Erdos335.IntermediateScale

/-!
# Uniform density control on moving windows

The prefix envelope controls every window inside an ambient cutoff. An
intermediate length dominating this envelope therefore preserves all three
ordinary densities on arbitrary moving windows.
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335

theorem prefixCount_positive_window (A : Set ℕ) (n L : ℕ) :
    prefixCount (tailShift A (n + 1)) L + count A n = count A (n + L) := by
  have h := prefixCount_add_tailShift A (n + 1) L
  rw [show n + 1 + L = n + L + 1 by omega,
    prefixCount_succ_eq_count, prefixCount_succ_eq_count] at h
  omega

theorem positive_window_error_le (A : Set ℕ) (d : ℝ) {n L N : ℕ} (hnL : n + L ≤ N) :
    |(prefixCount (tailShift A (n + 1)) L : ℝ) - d * L| ≤ 2 * prefixError A d N := by
  have h := prefixCount_positive_window A n L
  have hr : (prefixCount (tailShift A (n + 1)) L : ℝ) + count A n = count A (n + L) := by
    exact_mod_cast h
  have heq : (prefixCount (tailShift A (n + 1)) L : ℝ) - d * L =
      (count A (n + L) : ℝ) - count A n - d * L := by linarith
  rw [heq]
  exact window_error_le_prefixError A d hnL

theorem moving_window_density_of_prefix_error (A : Set ℕ) (d : ℝ)
    (N L t : ℕ → ℕ) (hL : ∀ᶠ k : ℕ in atTop, 0 < L k)
    (hinside : ∀ᶠ k : ℕ in atTop, t k + L k ≤ N k)
    (herror : Tendsto (fun k : ℕ => prefixError A d (N k) / L k) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => (prefixCount (tailShift A (t k + 1)) (L k) : ℝ) / L k)
      atTop (𝓝 d) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : Tendsto (fun k : ℕ => 2 * (prefixError A d (N k) / L k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul herror
  apply squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hbound
  filter_upwards [hL, hinside] with k hk hkn
  have hkR : (0 : ℝ) < L k := by exact_mod_cast hk
  have hcount := positive_window_error_le A d hkn
  rw [Real.norm_eq_abs]
  have heq : (prefixCount (tailShift A (t k + 1)) (L k) : ℝ) / L k - d =
      ((prefixCount (tailShift A (t k + 1)) (L k) : ℝ) - d * L k) / L k := by
    field_simp
  rw [heq, abs_div, abs_of_pos hkR]
  calc
    _ ≤ (2 * prefixError A d (N k)) / L k := div_le_div_of_nonneg_right hcount hkR.le
    _ = _ := by ring

theorem prefix_error_control_of_scale_domination (A : Set ℕ) (d : ℝ)
    (N L H : ℕ → ℕ) (hL : ∀ k, 0 < L k)
    (herror : Tendsto (fun k : ℕ => prefixError A d (N k) / L k) atTop (𝓝 0))
    (hdom : Tendsto (fun k : ℕ => (L k : ℝ) / H k) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => prefixError A d (N k) / H k) atTop (𝓝 0) := by
  have h := herror.mul hdom
  simp only [mul_zero] at h
  apply h.congr
  intro k
  have hL0 : (L k : ℝ) ≠ 0 := by exact_mod_cast (hL k).ne'
  by_cases hH : H k = 0
  · simp [hH]
  · have hH0 : (H k : ℝ) ≠ 0 := by exact_mod_cast hH
    field_simp

end Erdos335
