import Erdos335.CyclicWindowDensities

/-!
# Window densities including a window beginning at zero
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem cyclicWindow_count_error_le (A : Set ℕ) (a : ℝ) (n q N : ℕ) [NeZero q]
    (hinside : n + q ≤ N) :
    |((cyclicWindow A n q).card : ℝ) - a * q| ≤ 2 * prefixError A a N + 2 := by
  rw [cyclicWindow_card_eq_prefixCount]
  have hsplit : (prefixCount A (n + q) : ℝ) =
      (prefixCount A n : ℝ) + prefixCount (tailShift A n) q := by
    exact_mod_cast prefixCount_add_tailShift A n q
  have hleft := abs_le.mp (prefixCount_error A (n + q))
  have hright := abs_le.mp (prefixCount_error A n)
  have hwindow := abs_le.mp (window_error_le_prefixError A a hinside)
  rw [abs_le]
  constructor <;> linarith

theorem cyclic_window_density_of_general_prefix_error (A : Set ℕ) (a : ℝ)
    (N q start : ℕ → ℕ) [∀ s, NeZero (q s)]
    (hq : Tendsto q atTop atTop)
    (hinside : ∀ᶠ s in atTop, start s + q s ≤ N s)
    (herror : Tendsto (fun s => prefixError A a (N s) / q s) atTop (𝓝 0)) :
    Tendsto (fun s => ((cyclicWindow A (start s) (q s)).card : ℝ) / q s) atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : Tendsto (fun s => 2 * (prefixError A a (N s) / q s) + 2 / q s)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, Function.comp_def] using (herror.const_mul 2).add
      ((tendsto_const_div_atTop_nhds_zero_nat 2).comp hq)
  apply squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hbound
  filter_upwards [hinside] with s hs
  have hqr : (0 : ℝ) < q s := by exact_mod_cast NeZero.pos (q s)
  have hb := div_le_div_of_nonneg_right
    (cyclicWindow_count_error_le A a (start s) (q s) (N s) hs) hqr.le
  rw [Real.norm_eq_abs]
  calc
    |((cyclicWindow A (start s) (q s)).card : ℝ) / q s - a| =
        |((cyclicWindow A (start s) (q s)).card : ℝ) - a * q s| / q s := by
      have heq : ((cyclicWindow A (start s) (q s)).card : ℝ) / q s - a =
          (((cyclicWindow A (start s) (q s)).card : ℝ) - a * q s) / q s := by
        field_simp
      rw [heq, abs_div, abs_of_pos hqr]
    _ ≤ (2 * prefixError A a (N s) + 2) / q s := hb
    _ = _ := by ring

end Erdos335.IntermediateScale
