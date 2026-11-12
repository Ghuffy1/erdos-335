import Erdos335.PrefixPolynomialTriangle
import Erdos335.AnnularBlockParameters

/-!
# Polynomial approximation of the ordinary limit of stitched block models
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem stitched_polynomial_approximation_of_limit
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ → ℕ} {ε : ℕ → ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (hH : ∀ s, 0 < H s) (hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (m : ∀ k s, BlockRegularModel F (H s) (L k) (ε k))
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) (w : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (happrox : ∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
      prefixEnergy (fun n => w n - stitchedBlockValue N hN (m k) n) (N (ρ s)) ≤ δ) :
    ∀ δ > 0, ∃ k : ℕ, ∀ᶠ s in atTop,
      (∑ n ∈ range (N (ρ s)), ‖(w n : ℂ) - stitchedBlockPolynomial N hN (m k) n‖ ^ 2) /
        N (ρ s) ≤ δ ^ 2 := by
  intro δ hδ
  have hquarter : (0 : ℝ) < δ ^ 2 / 4 := by positivity
  have heighth : (0 : ℝ) < δ ^ 2 / 8 := by positivity
  obtain ⟨K, hK⟩ := happrox (δ ^ 2 / 4) hquarter
  have hεsq : Tendsto (fun k => ε k ^ 2) atTop (𝓝 0) := by simpa using hε.pow 2
  obtain ⟨Kε, hKε⟩ := eventually_atTop.mp (hεsq.eventually (eventually_lt_nhds heighth))
  let k := max K Kε
  have hεk : ε k ^ 2 < δ ^ 2 / 8 := hKε k (le_max_right _ _)
  let e := fun s => ((L k : ℝ) + 1) ^ 2 *
    ((H (ρ s) : ℝ) / N (ρ s) + (N (ρ s - 1) : ℝ) / N (ρ s))
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [e, Function.comp_def, add_zero, mul_zero] using
      ((hHN.add hprev).comp hρ.tendsto_atTop).const_mul (((L k : ℝ) + 1) ^ 2)
  refine ⟨k, ?_⟩
  filter_upwards [hK k (le_max_left _ _), he.eventually (eventually_lt_nhds heighth),
    (hN.comp hρ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with s hs ht hNs
  have hmodel := stitchedBlock_prefix_approximation N hN hmono (m k) (ρ s) (hH (ρ s)) hNs
  have htriangle := prefix_polynomial_triangle w (stitchedBlockValue N hN (m k))
    (stitchedBlockPolynomial N hN (m k)) (N (ρ s))
  change _ ≤ ε k ^ 2 + e s at hmodel
  linarith

end Erdos335.IntermediateScale
