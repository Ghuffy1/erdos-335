import Erdos335.BlockWindowBoundaries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Vanishing density of windows that meet block boundaries
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Classical

namespace Erdos335.IntermediateScale

theorem block_crossing_density_bound (N H W : ℕ) (hN : 0 < N) (hH : 0 < H) :
    (((range N).filter (fun n => n / H ≠ (n + W) / H)).card : ℝ) / N ≤
      (W : ℝ) / H + (W : ℝ) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hcard : (((range N).filter (fun n => n / H ≠ (n + W) / H)).card : ℝ) ≤
      (((N / H : ℕ) : ℝ) + 1) * W := by exact_mod_cast block_crossing_window_card N H W hH
  have hquot : ((N / H : ℕ) : ℝ) ≤ (N : ℝ) / H := Nat.cast_div_le
  calc
    _ ≤ ((((N / H : ℕ) : ℝ) + 1) * W) / N := div_le_div_of_nonneg_right hcard hNr.le
    _ ≤ (((N : ℝ) / H + 1) * W) / N := by gcongr
    _ = _ := by field_simp

theorem block_crossing_density_tendsto_zero (N H W : ℕ → ℕ)
    (hN : ∀ᶠ s in atTop, 0 < N s) (hH : ∀ᶠ s in atTop, 0 < H s)
    (hWH : Tendsto (fun s => (W s : ℝ) / H s) atTop (𝓝 0))
    (hWN : Tendsto (fun s => (W s : ℝ) / N s) atTop (𝓝 0)) :
    Tendsto (fun s => (((range (N s)).filter
      (fun n => n / H s ≠ (n + W s) / H s)).card : ℝ) / N s) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_
    (by simpa only [add_zero] using hWH.add hWN)
  filter_upwards [hN, hH] with s hs ht
  exact block_crossing_density_bound (N s) (H s) (W s) hs ht

theorem block_quotient_constant (H n W j : ℕ)
    (heq : n / H = (n + W) / H) (hj : j ≤ W) : (n + j) / H = n / H := by
  have hlo : n / H ≤ (n + j) / H := Nat.div_le_div_right (Nat.le_add_right n j)
  have hhi : (n + j) / H ≤ (n + W) / H := Nat.div_le_div_right (Nat.add_le_add_left hj n)
  omega

theorem block_function_constant {E : Type*} (c : ℕ → E) (H n W j : ℕ)
    (heq : n / H = (n + W) / H) (hj : j ≤ W) : c ((n + j) / H) = c (n / H) := by
  rw [block_quotient_constant H n W j heq hj]

end Erdos335.IntermediateScale
