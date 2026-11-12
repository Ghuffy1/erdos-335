import Erdos335.DiagonalStructuredPeriods
import Erdos335.LinearConvolutionLimits
import Erdos335.IntermediateFourierDecomposition

/-!
# Convolution transfer and periods of an intermediate Fourier decomposition
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem intermediate_fourier_convolution_and_periods
    (R : ℕ) (hR : 0 < R) (F w : ℕ → ℝ) (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ n, w n ∈ Set.Icc (0 : ℝ) 1)
    (d : ℕ → ℕ) (c : ∀ k, ℕ → Fin (d k) → ℂ) (α : ∀ k, ℕ → Fin (d k) → ℝ)
    (hc : ∀ k n i, ‖c k n i‖ ≤ 1)
    (N A B : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (happrox : ∀ δ > 0, ∃ k : ℕ, ∀ᶠ s in atTop,
      (∑ n ∈ range (N s), ‖(w n : ℂ) - variableFrequencyPolynomial (c k) (α k) n‖ ^ 2) /
        N s ≤ δ ^ 2)
    (hcontrol : ∀ W : ℕ → ℕ, (∀ s, 0 < W s) →
      Tendsto (fun s => (A s : ℝ) / W s) atTop (𝓝 0) →
      Tendsto (fun s => (W s : ℝ) / B s) atTop (𝓝 0) →
      Tendsto (fun s => (∑ n ∈ range (N s),
        windowFourierNorm (fun n => F n - w n) n (W s)) / N s) atTop (𝓝 0) ∧
      (∀ k, Tendsto (fun s => ((varyingPolynomialParameters (N s) (W s) (c k) (α k)).card : ℝ) /
        N s) atTop (𝓝 0)) ∧
      ∀ k K : ℕ, 0 < K → Tendsto (fun s =>
        ((badFrequencyCombinationWindows (N s) (W s) K (α k)).card : ℝ) / N s) atTop (𝓝 0))
    (H : ℕ → ℕ) (hHpos : ∀ s, 0 < H s) (hH : Tendsto H atTop atTop)
    (hAH : Tendsto (fun s => (A s : ℝ) / H s) atTop (𝓝 0))
    (hHB : Tendsto (fun s => (H s : ℝ) / B s) atTop (𝓝 0))
    (hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0)) :
    (∀ g : ℕ → ℕ → ℂ, (∀ s n, ‖g s n‖ ≤ 1) →
      Tendsto (fun s => (∑ n ∈ range (N s),
        ‖linearWindowConvolution F (g s) (H s) n -
          linearWindowConvolution w (g s) (H s) n‖ ^ 2) / N s) atTop (𝓝 0)) ∧
    ∃ (Q : ℕ → ℕ → ℕ) (ε : ℕ → ℝ),
      (∀ s, 0 < ε s) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ᶠ s in atTop, ∀ n, H s ≤ Q s n ∧ (Q s n : ℝ) ≤ (1 + ε s) * H s) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, ∀ n, M ∣ Q s n) ∧
      Tendsto (fun s => averagedWindowTranslationError (fun n => (w n : ℂ))
        (Q s) (N s) (R * H s)) atTop (𝓝 0) := by
  have hscaled (C : ℕ) (hC : 0 < C) := by
    have hpos : ∀ s, 0 < C * H s := fun s => Nat.mul_pos hC (hHpos s)
    have hlo : Tendsto (fun s => (A s : ℝ) / (C * H s : ℕ)) atTop (𝓝 0) := by
      have heq : (fun s => (A s : ℝ) / (C * H s : ℕ)) =
          fun s => ((A s : ℝ) / H s) / C := by
        funext s
        push_cast
        ring
      rw [heq]
      simpa only [zero_div] using hAH.div_const (C : ℝ)
    have hhi : Tendsto (fun s => ((C * H s : ℕ) : ℝ) / B s) atTop (𝓝 0) := by
      simpa only [Nat.cast_mul, mul_div_assoc, mul_zero] using hHB.const_mul (C : ℝ)
    exact hcontrol (fun s => C * H s) hpos hlo hhi
  refine ⟨?_, ?_⟩
  · intro g hg
    exact structured_convolution_energy_tendsto_zero F w g hF hw hg N H hN hHpos hHN
      (hscaled 2 (by decide)).1
  · have hparams : ∀ k, Tendsto (fun s =>
        ((varyingPolynomialParameters (N s) (3 * (R * H s)) (c k) (α k)).card : ℝ) / N s)
        atTop (𝓝 0) := by
      simpa only [Nat.mul_assoc] using (hscaled (3 * R) (by omega)).2.1
    exact exists_asymptotic_structured_periods R hR w hw d c α hc N H hN hH hHN happrox
      hparams (hcontrol H hHpos hAH hHB).2.2

end Erdos335.IntermediateScale
