import Erdos335.PrefixBlockStitching

/-!
# An ordinary bounded representative of a mean-square Cauchy family
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_prefix_mean_square_limit
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (f : ℕ → ℕ → ℝ) (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpair : ∀ l k, k ≤ l → ∀ᶠ s in atTop,
      (∑ n ∈ range (N s), (f l n - f k n) ^ 2) / N s ≤ ε k) :
    ∃ g : ℕ → ℝ, (∀ n, g n ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        (∑ n ∈ range (N s), (g n - f k n) ^ 2) / N s ≤ δ := by
  obtain ⟨k, g, _, hg, _, happrox⟩ := exists_prefix_stitched_approximation N hN hmono f hf ε hpair
  refine ⟨g, hg, fun δ hδ => ?_⟩
  have hhalf : (0 : ℝ) < δ / 2 := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hε.eventually (eventually_lt_nhds hhalf))
  refine ⟨K, fun j hj => ?_⟩
  filter_upwards [happrox j, hratio.eventually (eventually_lt_nhds hhalf)] with s hs hsmall
  have he := hK j hj
  linarith

end Erdos335.IntermediateScale
