import Erdos335.PrefixApproximateOrthogonality
import Erdos335.PrefixMeanSquareLimit
import Erdos335.PrefixCorrelationContinuity
import Erdos335.PrefixMeanContinuity

/-!
# Limits of bounded approximate decompositions along sparse prefixes

This implements the bounded real-valued case of the approximation argument
used by Ackelsberg--Richter, Lemma 7.12, along prefixes with vanishing previous
prefix ratio.
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_bounded_prefix_decomposition_limit
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (F : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (ε : ℕ → ℝ)
    (hA : ∀ k, Tendsto (fun s => prefixEnergy (f k) (N s)) atTop (𝓝 (A k)))
    (hB : ∀ k l, Tendsto (fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s))
      atTop (𝓝 (B k l))) (hown : ∀ k, B k k = 0)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |B k l| ≤ ε k) :
    ∃ g : ℕ → ℝ, (∀ n, g n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => g n - f k n) (N s) ≤ δ) ∧
      Tendsto (fun s => prefixCorrelation g (fun n => F n - g n) (N s)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hpair⟩ := exists_vanishing_prefix_cauchy_bound N F f hf A B ε hA hB hown hε hcross
  obtain ⟨g, hg, happrox⟩ := exists_prefix_mean_square_limit N hN hmono hratio f hf δ hδ hpair
  refine ⟨g, hg, happrox, ?_⟩
  apply prefix_orthogonality_limit N F g f hF hg hf happrox
  intro k
  simpa only [hown] using hB k k

theorem exists_mean_preserving_prefix_decomposition_limit
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (F : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (ε : ℕ → ℝ)
    (hA : ∀ k, Tendsto (fun s => prefixEnergy (f k) (N s)) atTop (𝓝 (A k)))
    (hB : ∀ k l, Tendsto (fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s))
      atTop (𝓝 (B k l))) (hown : ∀ k, B k k = 0)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |B k l| ≤ ε k)
    (hmean : ∀ k, Tendsto (fun s => prefixCorrelation (fun n => F n - f k n) (fun _ => 1) (N s))
      atTop (𝓝 0)) :
    ∃ g : ℕ → ℝ, (∀ n, g n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => g n - f k n) (N s) ≤ δ) ∧
      Tendsto (fun s => prefixCorrelation g (fun n => F n - g n) (N s)) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixCorrelation (fun n => F n - g n) (fun _ => 1) (N s)) atTop (𝓝 0) := by
  obtain ⟨g, hg, happrox, horth⟩ := exists_bounded_prefix_decomposition_limit
    N hN hmono hratio F f hF hf A B ε hA hB hown hε hcross
  exact ⟨g, hg, happrox, horth, prefix_mean_preservation_limit N F g f happrox hmean⟩

end Erdos335.IntermediateScale
