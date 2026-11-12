import Erdos335.FrequencyScaleSelection
import Erdos335.FrequencyCombinationWindows

/-!
# Simultaneous frequency separation for countably many polynomial models
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem exists_polynomial_frequency_scale_selection
    (N : ℕ → ℕ) [∀ s, NeZero (N s)] (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (L : ℕ → ℕ) (α : ∀ k, ℕ → Fin (L k) → ℝ) :
    ∃ (A B σ : ℕ → ℕ), StrictMono σ ∧
      (∀ s, 0 < A s ∧ 0 < B s) ∧
      Tendsto (fun s => (lower s : ℝ) / A s) atTop (𝓝 0) ∧
      Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0) ∧
      Tendsto (fun s => (B s : ℝ) / upper s) atTop (𝓝 0) ∧
      ∀ W : ℕ → ℕ, (∀ᶠ s in atTop, 0 < W s) →
        Tendsto (fun s => (A (σ s) : ℝ) / W s) atTop (𝓝 0) →
        Tendsto (fun s => (W s : ℝ) / B (σ s)) atTop (𝓝 0) →
        ∀ k C : ℕ, 0 < C → Tendsto
          (fun s => ((badFrequencyCombinationWindows (N (σ s)) (W s) C (α k)).card : ℝ) / N (σ s))
          atTop (𝓝 0) := by
  let J := Σ k : ℕ, Fin (L k) → ℤ
  let v : J → ℕ → ℕ → ℝ := fun j _ n => circleFrequencyDistance (frequencyCombination (α j.1) j.2 n)
  obtain ⟨A, B, σ, hσ, hpos, hlow, hAB, hhigh, hbands⟩ :=
    exists_frequency_scale_selection N lower upper hlower hupper hgap U hU v
  refine ⟨A, B, σ, hσ, hpos, hlow, hAB, hhigh, ?_⟩
  intro W hW hAW hWB k C hC
  apply badFrequencyCombinationWindows_density_tendsto_zero (N ∘ σ) W C (α k)
  intro w
  exact hbands (⟨k, fun i => (w i).val⟩ : J) W hW hAW hWB C hC

end Erdos335.IntermediateScale
