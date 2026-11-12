import Erdos335.FilteredPrefixDecomposition

/-!
# Prefix decompositions that preserve additional countable limits
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem exists_filtered_prefix_decomposition_with_tests
    {J : Type*} [Countable J]
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
      U (𝓝 0))
    (T : J → ℕ → ℝ) (t : J → ℝ) (hT : ∀ j, Tendsto (T j) U (𝓝 (t j))) :
    ∃ (ρ : ℕ → ℕ) (g : ℕ → ℝ), StrictMono ρ ∧
      (∀ n, g n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => g n - f k n) (N (ρ s)) ≤ δ) ∧
      Tendsto (fun s => prefixCorrelation g (fun n => F n - g n) (N (ρ s))) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixCorrelation (fun n => F n - g n) (fun _ => 1) (N (ρ s))) atTop (𝓝 0) ∧
      ∀ j, Tendsto (fun s => T j (ρ s)) atTop (𝓝 (t j)) := by
  let C : ℕ ⊕ ((ℕ × ℕ) ⊕ (ℕ ⊕ J)) → ℕ → ℝ
    | .inl k => fun s => prefixEnergy (f k) (N s)
    | .inr (.inl (k, l)) => fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s)
    | .inr (.inr (.inl k)) => fun s => prefixCorrelation (fun n => F n - f k n) (fun _ => 1) (N s)
    | .inr (.inr (.inr j)) => T j
  let c : ℕ ⊕ ((ℕ × ℕ) ⊕ (ℕ ⊕ J)) → ℝ
    | .inl k => A k
    | .inr (.inl (k, l)) => B k l
    | .inr (.inr (.inl _)) => 0
    | .inr (.inr (.inr j)) => t j
  have hC : ∀ j, Tendsto (C j) U (𝓝 (c j)) := by
    rintro (k | (⟨k, l⟩ | (k | j)))
    · exact hA k
    · exact hB k l
    · exact hmean k
    · exact hT j
  obtain ⟨σ, hσ, hlim⟩ := exists_common_filtered_correlation_subsequence U hU C c hC
  obtain ⟨τ, g, hτ, hg, happrox, horth, hzero⟩ := exists_filtered_prefix_decomposition
    atTop le_rfl (N ∘ σ) (hN.comp hσ.tendsto_atTop) F f hF hf A B ε
    (fun k => hlim (.inl k)) (fun k l => hlim (.inr (.inl (k, l)))) hown hε hcross
    (fun k => hlim (.inr (.inr (.inl k))))
  exact ⟨σ ∘ τ, g, hσ.comp hτ, hg, happrox, horth, hzero,
    fun j => (hlim (.inr (.inr (.inr j)))).comp hτ.tendsto_atTop⟩

end Erdos335.IntermediateScale
