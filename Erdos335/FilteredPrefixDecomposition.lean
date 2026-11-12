import Erdos335.CountableCorrelationSubsequence
import Erdos335.BoundedPrefixDecompositionLimit
import Erdos335.SparsePrefixSubsequence

/-!
# Recovering an ordinary prefix decomposition from filtered correlations
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem exists_filtered_prefix_decomposition
    (U : Filter ℕ) [NeBot U] (hU : U ≤ atTop)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (F : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (ε : ℕ → ℝ)
    (hA : ∀ k, Tendsto (fun s => prefixEnergy (f k) (N s)) U (𝓝 (A k)))
    (hB : ∀ k l, Tendsto (fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s))
      U (𝓝 (B k l))) (hown : ∀ k, B k k = 0)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |B k l| ≤ ε k)
    (hmean : ∀ k, Tendsto (fun s => prefixCorrelation (fun n => F n - f k n) (fun _ => 1) (N s))
      U (𝓝 0)) :
    ∃ (ρ : ℕ → ℕ) (g : ℕ → ℝ), StrictMono ρ ∧
      (∀ n, g n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => g n - f k n) (N (ρ s)) ≤ δ) ∧
      Tendsto (fun s => prefixCorrelation g (fun n => F n - g n) (N (ρ s))) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixCorrelation (fun n => F n - g n) (fun _ => 1) (N (ρ s))) atTop (𝓝 0) := by
  let C : ℕ ⊕ ((ℕ × ℕ) ⊕ ℕ) → ℕ → ℝ
    | .inl k => fun s => prefixEnergy (f k) (N s)
    | .inr (.inl (k, l)) => fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s)
    | .inr (.inr k) => fun s => prefixCorrelation (fun n => F n - f k n) (fun _ => 1) (N s)
  let a : ℕ ⊕ ((ℕ × ℕ) ⊕ ℕ) → ℝ
    | .inl k => A k
    | .inr (.inl (k, l)) => B k l
    | .inr (.inr _) => 0
  have hC : ∀ j, Tendsto (C j) U (𝓝 (a j)) := by
    rintro (k | (⟨k, l⟩ | k))
    · exact hA k
    · exact hB k l
    · exact hmean k
  obtain ⟨σ, hσ, hlimits⟩ := exists_common_filtered_correlation_subsequence U hU C a hC
  obtain ⟨τ, hτ, hNt, hratio⟩ := exists_sparse_prefix_subsequence (N ∘ σ) (hN.comp hσ.tendsto_atTop)
  let ρ := σ ∘ τ
  have hρ : StrictMono ρ := hσ.comp hτ
  have hρN : Tendsto (N ∘ ρ) atTop atTop := hN.comp hρ.tendsto_atTop
  have hA' (k : ℕ) : Tendsto (fun s => prefixEnergy (f k) ((N ∘ ρ) s)) atTop (𝓝 (A k)) :=
    (hlimits (.inl k)).comp hτ.tendsto_atTop
  have hB' (k l : ℕ) : Tendsto
      (fun s => prefixCorrelation (f k) (fun n => F n - f l n) ((N ∘ ρ) s)) atTop (𝓝 (B k l)) :=
    (hlimits (.inr (.inl (k, l)))).comp hτ.tendsto_atTop
  have hmean' (k : ℕ) : Tendsto
      (fun s => prefixCorrelation (fun n => F n - f k n) (fun _ => 1) ((N ∘ ρ) s)) atTop (𝓝 0) :=
    (hlimits (.inr (.inr k))).comp hτ.tendsto_atTop
  obtain ⟨g, hg, happrox, horth, hzeromean⟩ := exists_mean_preserving_prefix_decomposition_limit
    (N ∘ ρ) hρN hNt.monotone hratio F f hF hf A B ε hA' hB' hown hε hcross hmean'
  exact ⟨ρ, g, hρ, hg, happrox, horth, hzeromean⟩

end Erdos335.IntermediateScale
