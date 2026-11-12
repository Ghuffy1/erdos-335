import Erdos335.CountableCorrelationSubsequence
import Erdos335.PrefixApproximateOrthogonality

/-!
# Convergence of prefix energies defined along a finer filter
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem filtered_prefix_energy_cauchy (U : Filter ℕ) [NeBot U] (hU : U ≤ atTop)
    (N : ℕ → ℕ) (F : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (ε : ℕ → ℝ)
    (hA : ∀ k, Tendsto (fun s => prefixEnergy (f k) (N s)) U (𝓝 (A k)))
    (hB : ∀ k l, Tendsto (fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s))
      U (𝓝 (B k l))) (hown : ∀ k, B k k = 0)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |B k l| ≤ ε k) : CauchySeq A := by
  let C : ℕ ⊕ (ℕ × ℕ) → ℕ → ℝ
    | .inl k => fun s => prefixEnergy (f k) (N s)
    | .inr (k, l) => fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s)
  let a : ℕ ⊕ (ℕ × ℕ) → ℝ
    | .inl k => A k
    | .inr (k, l) => B k l
  have hC : ∀ j, Tendsto (C j) U (𝓝 (a j)) := by
    rintro (k | ⟨k, l⟩)
    · exact hA k
    · exact hB k l
  obtain ⟨σ, _, hσ⟩ := exists_common_filtered_correlation_subsequence U hU C a hC
  apply prefix_energy_cauchy_of_approximate_orthogonality (N ∘ σ) F f hf A B ε
    (fun k => hσ (.inl k)) (fun k l => hσ (.inr (k, l))) hown hε hcross

end Erdos335.IntermediateScale
