import Erdos335.WindowFourierContinuity

/-!
# Passing averaged Fourier uniformity through mean-square approximation
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem averaged_windowFourierNorm_tendsto_zero
    (N W : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hW : ∀ᶠ s in atTop, 0 < W s)
    (hWN : Tendsto (fun s => (W s : ℝ) / N s) atTop (𝓝 0))
    (r : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hr : ∀ n, |r n| ≤ 1) (hf : ∀ k n, |f k n| ≤ 1)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (happrox : ∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
      prefixEnergy (fun n => r n - f k n) (N s) ≤ δ ^ 2)
    (huniform : ∀ k, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ s in atTop,
      (∑ n ∈ range (N s), windowFourierNorm (f k) n (W s)) / N s ≤ ε k + e s) :
    Tendsto (fun s => (∑ n ∈ range (N s), windowFourierNorm r n (W s)) / N s)
      atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun s => ha.trans_le (div_nonneg
      (sum_nonneg fun n hn => windowFourierNorm_nonneg r n (W s)) (Nat.cast_nonneg _))
  · intro b hb
    have hquarter : (0 : ℝ) < b / 4 := by positivity
    obtain ⟨K, hK⟩ := happrox (b / 4) hquarter
    obtain ⟨Kε, hKε⟩ := eventually_atTop.mp (hε.eventually (eventually_lt_nhds hquarter))
    let k := max K Kε
    have hεk : ε k < b / 4 := hKε k (le_max_right _ _)
    obtain ⟨e, he, hu⟩ := huniform k
    have hWsmall := (hWN.const_mul 2).eventually (eventually_lt_nhds (by simpa only [mul_zero] using hquarter))
    filter_upwards [hK k (le_max_left _ _), hu, he.eventually (eventually_lt_nhds hquarter),
      hWsmall, hW, hN.eventually (eventually_gt_atTop 0)] with s hs ht heS hwS hWs hNs
    have hc := averaged_windowFourierNorm_difference_bound r (f k) hr (hf k)
      (N s) (W s) hNs hWs (b / 4) hquarter.le hs
    have hwS' : 2 * (W s : ℝ) / N s < b / 4 := by simpa only [mul_div_assoc] using hwS
    linarith

end Erdos335.IntermediateScale
