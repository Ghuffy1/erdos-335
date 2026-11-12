import Erdos335.FilteredTwoPrefixDecomposition
import Erdos335.LoebPrefixDistances

/-!
# Ordinary bounded representatives of two equal Loeb limits
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped InnerProductSpace

namespace Erdos335.Loeb

open Erdos335.IntermediateScale

theorem exists_ordinary_realization_of_equal_loeb_limits
    (N : ℕ → ℕ) [∀ s, NeZero (N s)] (hN : Tendsto N atTop atTop)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ℕ → ℝ) (f g : ℕ → ℕ → ℝ)
    (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (hf : ∀ k n, f k n ∈ Icc (0 : ℝ) 1) (hg : ∀ k n, g k n ∈ Icc (0 : ℝ) 1)
    (v : Lp ℝ 2 (loebMeasure (X := fun s => Fin (N s)) U hU))
    (hfLim : Tendsto (fun k => prefixLoebVector N U hU (f k) (hf k)) atTop (𝓝 v))
    (hgLim : Tendsto (fun k => prefixLoebVector N U hU (g k) (hg k)) atTop (𝓝 v))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hown : ∀ k, ⟪prefixLoebVector N U hU (f k) (hf k),
      prefixLoebVector N U hU F hF - prefixLoebVector N U hU (f k) (hf k)⟫_ℝ = 0)
    (hcross : ∀ k l, k ≤ l → |⟪prefixLoebVector N U hU (f k) (hf k),
      prefixLoebVector N U hU F hF - prefixLoebVector N U hU (f l) (hf l)⟫_ℝ| ≤ ε k)
    (hmean : ∀ k, Tendsto (fun s => prefixCorrelation (fun n => F n - f k n) (fun _ => 1) (N s))
      (U : Filter ℕ) (𝓝 0)) :
    ∃ (ρ : ℕ → ℕ) (w : ℕ → ℝ), StrictMono ρ ∧
      (∀ n, w n ∈ Icc (0 : ℝ) 1) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => w n - f k n) (N (ρ s)) ≤ δ) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => w n - g k n) (N (ρ s)) ≤ δ) ∧
      Tendsto (fun s => prefixCorrelation w (fun n => F n - w n) (N (ρ s))) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixCorrelation (fun n => F n - w n) (fun _ => 1) (N (ρ s))) atTop (𝓝 0) := by
  let A := fun k => ‖prefixLoebVector N U hU (f k) (hf k)‖ ^ 2
  let B := fun k l => ⟪prefixLoebVector N U hU (f k) (hf k),
    prefixLoebVector N U hU F hF - prefixLoebVector N U hU (f l) (hf l)⟫_ℝ
  let D := fun k => ‖prefixLoebVector N U hU (f k) (hf k) -
    prefixLoebVector N U hU (g k) (hg k)‖ ^ 2
  have hD : Tendsto D atTop (𝓝 0) := by
    simpa [D] using (hfLim.sub hgLim).norm.pow 2
  exact exists_filtered_two_prefix_decomposition (U : Filter ℕ) hU N hN F f g hF hf A B ε D
    (fun k => tendsto_prefixLoebVector_energy N U hU (f k) (hf k))
    (fun k l => tendsto_prefixLoebVector_residual_correlation N U hU F (f k) (f l) hF (hf k) (hf l))
    hown hε hcross hmean hD
    (fun k => tendsto_prefixLoebVector_distance N U hU (f k) (g k) (hf k) (hg k))

end Erdos335.Loeb
