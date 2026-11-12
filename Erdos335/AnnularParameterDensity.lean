import Erdos335.AnnularParameterWindows
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Vanishing density of variation in stitched polynomial parameters
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Erdos335.IntermediateScale

theorem varyingParameterWindows_density_bound
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (s W : ℕ)
    (hHs : 0 < H s) (hNs : 0 < N s) :
    ((varyingParameterWindows N hN m s W).card : ℝ) / N s ≤
      (N (s - 1) : ℝ) / N s + (W : ℝ) / H s + 2 * (W : ℝ) / N s := by
  have hNr : (0 : ℝ) < N s := by exact_mod_cast hNs
  have hcard : ((varyingParameterWindows N hN m s W).card : ℝ) ≤
      N (s - 1) + W + (((N s / H s : ℕ) : ℝ) + 1) * W := by
    exact_mod_cast varyingParameterWindows_card N hN hmono m s W hHs
  have hquot : ((N s / H s : ℕ) : ℝ) ≤ (N s : ℝ) / H s := Nat.cast_div_le
  calc
    _ ≤ (N (s - 1) + W + (((N s / H s : ℕ) : ℝ) + 1) * W) / N s :=
      div_le_div_of_nonneg_right hcard hNr.le
    _ ≤ (N (s - 1) + W + ((N s : ℝ) / H s + 1) * W) / N s := by gcongr
    _ = _ := by field_simp; ring

theorem varyingParameterWindows_density_tendsto_zero
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (W : ℕ → ℕ)
    (hH : ∀ᶠ s in atTop, 0 < H s)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (hWH : Tendsto (fun s => (W s : ℝ) / H s) atTop (𝓝 0))
    (hWN : Tendsto (fun s => (W s : ℝ) / N s) atTop (𝓝 0)) :
    Tendsto (fun s => ((varyingParameterWindows N hN m s (W s)).card : ℝ) / N s)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_
    (by simpa only [zero_add, mul_zero] using (hprev.add hWH).add (hWN.const_mul 2))
  filter_upwards [hH, hN.eventually (eventually_gt_atTop 0)] with s hs hNs
  simpa only [mul_div_assoc] using
    varyingParameterWindows_density_bound N hN hmono m s (W s) hs hNs

end Erdos335.IntermediateScale
