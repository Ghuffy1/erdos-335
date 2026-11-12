import Erdos335.PrefixCorrelationPatching

/-!
# Correlations of sparse-prefix stitched block models
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem sparse_stitch_cross_correlation
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (F : ℕ → ℝ) (f g : ℕ → ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ s n, f s n ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ s n, g s n ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun s =>
      prefixCorrelation (prefixStitch N hN f id)
        (fun n => F n - prefixStitch N hN g id n) (N s) -
      prefixCorrelation (f s) (fun n => F n - g s n) (N s)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun s => abs_nonneg _) ?_
    (by simpa only [mul_zero] using hratio.const_mul 2)
  intro s
  rw [← mul_div_assoc]
  apply prefix_patch_correlation_bound F (prefixStitch N hN f id) (prefixStitch N hN g id)
    (f s) (g s) (N s) (N (s - 1)) hF
    (prefixStitch_bounds N hN f hf id) (prefixStitch_bounds N hN g hg id) (hf s) (hg s)
  intro n hlow hhigh
  simp only [prefixStitch, firstCutIndex_eq N hN hmono s n hhigh hlow, id_eq, and_self]

end Erdos335.IntermediateScale
