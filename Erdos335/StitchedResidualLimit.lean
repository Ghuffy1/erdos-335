import Erdos335.WindowFourierApproximationLimit
import Erdos335.AnnularFourierAverage

/-!
# Fourier uniformity of the residual of an ordinary stitched-model limit
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem stitched_residual_uniformity_of_limit
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ → ℕ} {ε : ℕ → ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (hH : ∀ s, 0 < H s) (m : ∀ k s, BlockRegularModel F (H s) (L k) (ε k))
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) (w : ℕ → ℝ) (hw : ∀ n, w n ∈ Set.Icc (0 : ℝ) 1)
    (hε0 : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hε : Tendsto ε atTop (𝓝 0))
    (happrox : ∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
      prefixEnergy (fun n => w n - stitchedBlockValue N hN (m k) n) (N (ρ s)) ≤ δ)
    (W : ℕ → ℕ) (hW : ∀ᶠ s in atTop, 0 < W s)
    (hHW : Tendsto (fun s => (H (ρ s) : ℝ) / W s) atTop (𝓝 0))
    (hWN : Tendsto (fun s => (W s : ℝ) / N (ρ s)) atTop (𝓝 0)) :
    Tendsto (fun s => (∑ n ∈ range (N (ρ s)), windowFourierNorm (fun n => F n - w n) n (W s)) /
      N (ρ s)) atTop (𝓝 0) := by
  let r := fun n => F n - w n
  let f := fun k n => F n - stitchedBlockValue N hN (m k) n
  have hr (n : ℕ) : |r n| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> dsimp [r] <;> linarith [(hF n).1, (hF n).2, (hw n).1, (hw n).2]
  have hf (k n : ℕ) : |f k n| ≤ 1 := stitched_residual_abs_le_one N hN (m k) hF n
  apply averaged_windowFourierNorm_tendsto_zero (N ∘ ρ) W (hN.comp hρ.tendsto_atTop)
    hW hWN r f hr hf ε hε
  · intro δ hδ
    obtain ⟨K, hK⟩ := happrox (δ ^ 2) (by positivity)
    refine ⟨K, fun k hk => ?_⟩
    have heq : (fun n => r n - f k n) =
        fun n => -(w n - stitchedBlockValue N hN (m k) n) := by
      funext n
      dsimp [r, f]
      ring
    rw [heq]
    simpa only [Function.comp_def, prefixEnergy, neg_sq] using hK k hk
  · intro k
    let e := fun s => 3 * ((H (ρ s) : ℝ) / W s) +
      (N (ρ s - 1) : ℝ) / N (ρ s) + (W s : ℝ) / N (ρ s)
    have he : Tendsto e atTop (𝓝 0) := by
      simpa only [e, Function.comp_def, mul_zero, add_zero] using
        ((hHW.const_mul 3).add (hprev.comp hρ.tendsto_atTop)).add hWN
    refine ⟨e, he, ?_⟩
    filter_upwards [hW, (hN.comp hρ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with s hs ht
    have hb := stitched_residual_fourier_average_bound N hN hmono (m k) hF
      (hε0 k) (hε1 k) (ρ s) (W s) (hH (ρ s)) hs ht
    calc
      _ ≤ ε k + 3 * (H (ρ s) : ℝ) / W s + ((N (ρ s - 1) : ℝ) + W s) / N (ρ s) := hb
      _ = _ := by dsimp [e]; ring

end Erdos335.IntermediateScale
