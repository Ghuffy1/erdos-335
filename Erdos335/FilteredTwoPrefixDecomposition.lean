import Erdos335.FilteredPrefixWithTests
import Erdos335.PrefixEnergyTriangle

/-!
# An ordinary bounded representative for two asymptotically equal approximation families
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem exists_filtered_two_prefix_decomposition
    (U : Filter ℕ) [NeBot U] (hU : U ≤ atTop)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (F : ℕ → ℝ) (f g : ℕ → ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (ε D : ℕ → ℝ)
    (hA : ∀ k, Tendsto (fun s => prefixEnergy (f k) (N s)) U (𝓝 (A k)))
    (hB : ∀ k l, Tendsto (fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s))
      U (𝓝 (B k l))) (hown : ∀ k, B k k = 0)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |B k l| ≤ ε k)
    (hmean : ∀ k, Tendsto (fun s => prefixCorrelation (fun n => F n - f k n) (fun _ => 1) (N s))
      U (𝓝 0))
    (hD : Tendsto D atTop (𝓝 0))
    (hprobe : ∀ k, Tendsto (fun s => prefixEnergy (fun n => f k n - g k n) (N s)) U (𝓝 (D k))) :
    ∃ (ρ : ℕ → ℕ) (v : ℕ → ℝ), StrictMono ρ ∧
      (∀ n, v n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => v n - f k n) (N (ρ s)) ≤ δ) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => v n - g k n) (N (ρ s)) ≤ δ) ∧
      Tendsto (fun s => prefixCorrelation v (fun n => F n - v n) (N (ρ s))) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixCorrelation (fun n => F n - v n) (fun _ => 1) (N (ρ s))) atTop (𝓝 0) := by
  obtain ⟨ρ, v, hρ, hv, happrox, horth, hzero, htest⟩ := exists_filtered_prefix_decomposition_with_tests
    U hU N hN F f hF hf A B ε hA hB hown hε hcross hmean
    (fun k s => prefixEnergy (fun n => f k n - g k n) (N s)) D hprobe
  refine ⟨ρ, v, hρ, hv, happrox, ?_, horth, hzero⟩
  intro δ hδ
  obtain ⟨Kf, hKf⟩ := happrox (δ / 4) (by positivity)
  obtain ⟨Kd, hKd⟩ := eventually_atTop.mp (hD.eventually (eventually_lt_nhds (show (0 : ℝ) < δ / 8 by positivity)))
  refine ⟨max Kf Kd, fun k hk => ?_⟩
  have hdk : D k < δ / 4 := lt_trans (hKd k ((le_max_right _ _).trans hk)) (by linarith)
  filter_upwards [hKf k ((le_max_left _ _).trans hk),
    (htest k).eventually (eventually_lt_nhds hdk)] with s hs ht
  have htriangle := prefixEnergy_triangle v (f k) (g k) (N (ρ s))
  linarith

end Erdos335.IntermediateScale
