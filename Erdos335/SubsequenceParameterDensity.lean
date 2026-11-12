import Erdos335.AnnularParameterDensity

/-!
# Variation of polynomial parameters along a selected prefix subsequence
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem varyingParameterWindows_density_along_subsequence
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (hH : ∀ s, 0 < H s)
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) (W : ℕ → ℕ)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (hWH : Tendsto (fun s => (W s : ℝ) / H (ρ s)) atTop (𝓝 0))
    (hWN : Tendsto (fun s => (W s : ℝ) / N (ρ s)) atTop (𝓝 0)) :
    Tendsto (fun s => ((varyingParameterWindows N hN m (ρ s) (W s)).card : ℝ) / N (ρ s))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_
    (by simpa only [zero_add, mul_zero] using
      ((hprev.comp hρ.tendsto_atTop).add hWH).add (hWN.const_mul 2))
  filter_upwards [(hN.comp hρ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with s hs
  simpa only [Function.comp_def, mul_div_assoc] using
    varyingParameterWindows_density_bound N hN hmono m (ρ s) (W s) (hH (ρ s)) hs

theorem window_ratio_tendsto_zero_of_intermediate
    (N H W : ℕ → ℕ) (hH : ∀ s, 0 < H s)
    (hWH : Tendsto (fun s => (W s : ℝ) / H s) atTop (𝓝 0))
    (hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0)) :
    Tendsto (fun s => (W s : ℝ) / N s) atTop (𝓝 0) := by
  have hprod := hWH.mul hHN
  simp only [mul_zero] at hprod
  apply hprod.congr
  intro s
  have hHs : (H s : ℝ) ≠ 0 := by exact_mod_cast (hH s).ne'
  field_simp

end Erdos335.IntermediateScale
