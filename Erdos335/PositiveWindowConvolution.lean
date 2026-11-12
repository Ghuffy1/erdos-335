import Erdos335.LinearConvolutionLimits

/-!
# Positive-index window convolution
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

noncomputable def positiveWindowConvolution (f : ℕ → ℝ) (g : ℕ → ℂ) (H n : ℕ) : ℂ :=
  (∑ m ∈ range H, (f (n - (m + 1)) : ℂ) * g (m + 1)) / (H : ℂ)

theorem positiveWindowConvolution_succ (f : ℕ → ℝ) (g : ℕ → ℂ) (H n : ℕ) :
    positiveWindowConvolution f g H (n + 1) =
      linearWindowConvolution f (fun m => g (m + 1)) H n := by
  simp only [positiveWindowConvolution, linearWindowConvolution, Nat.add_sub_add_right]

theorem positive_structured_convolution_energy_tendsto_zero
    (f w : ℕ → ℝ) (g : ℕ → ℕ → ℂ)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ n, w n ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ s n, ‖g s n‖ ≤ 1)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hH : ∀ s, 0 < H s)
    (hscale : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (hFourier : Tendsto (fun s =>
      (∑ n ∈ range (N s), windowFourierNorm (fun k => f k - w k) n (2 * H s)) / N s)
      atTop (𝓝 0)) :
    Tendsto (fun s => (∑ n ∈ range (N s),
      ‖positiveWindowConvolution f (g s) (H s) (n + 1) -
        positiveWindowConvolution w (g s) (H s) (n + 1)‖ ^ 2) / N s) atTop (𝓝 0) := by
  simpa only [positiveWindowConvolution_succ] using
    structured_convolution_energy_tendsto_zero f w (fun s m => g s (m + 1))
      hf hw (fun s m => hg s (m + 1)) N H hN hH hscale hFourier

end Erdos335.IntermediateScale
