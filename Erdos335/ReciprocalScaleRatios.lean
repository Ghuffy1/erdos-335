import Erdos335.FrequencyThresholdProfiles

/-!
# Reversing a vanishing ratio between positive integer scales
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem reciprocal_scale_ratio_tendsto_atTop (A B : ℕ → ℕ)
    (hA : ∀ s, 0 < A s) (hB : ∀ s, 0 < B s)
    (hratio : Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0)) :
    Tendsto (fun s => (B s : ℝ) / A s) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  let T := max M 0 + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hMT : M < T := by dsimp [T]; linarith [le_max_left M 0]
  filter_upwards [hratio.eventually (eventually_lt_nhds (one_div_pos.mpr hT))] with s hs
  have hAr : (0 : ℝ) < A s := by exact_mod_cast hA s
  have hBr : (0 : ℝ) < B s := by exact_mod_cast hB s
  have hprod : (A s : ℝ) * T < B s := by
    simpa only [one_mul] using (div_lt_div_iff₀ hBr hT).mp hs
  apply (le_div_iff₀ hAr).mpr
  nlinarith

theorem scale_tendsto_atTop_of_smaller (A B : ℕ → ℕ)
    (hA : Tendsto A atTop atTop) (hB : ∀ s, 0 < B s)
    (hratio : Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0)) :
    Tendsto B atTop atTop := by
  apply tendsto_atTop_mono' atTop _ hA
  exact eventually_scale_le_of_ratio_zero A B hB hratio

end Erdos335.IntermediateScale
