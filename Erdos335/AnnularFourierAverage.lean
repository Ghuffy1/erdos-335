import Erdos335.ExceptionalWindowAverage
import Erdos335.AnnularBlockModels

/-!
# Averaged moving-window uniformity of stitched block residuals
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem stitched_residual_abs_le_one
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    |F n - stitchedBlockValue N hN m n| ≤ 1 := by
  apply abs_le.mpr
  have hm := stitchedBlockValue_mem N hN m n
  constructor <;> linarith [(hF n).1, (hF n).2, hm.1, hm.2]

theorem stitched_residual_fourier_average_bound
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (m : ∀ s, BlockRegularModel F (H s) L ε)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (s W : ℕ) (hH : 0 < H s) (hW : 0 < W) (hNs : 0 < N s) :
    (∑ n ∈ range (N s), windowFourierNorm (fun k => F k - stitchedBlockValue N hN m k) n W) / N s ≤
      ε + 3 * (H s : ℝ) / W + ((N (s - 1) : ℝ) + W) / N s := by
  let r := fun k => F k - stitchedBlockValue N hN m k
  let E := (range (N s)).filter (fun n => n < N (s - 1) ∨ N s ≤ n + W)
  let A := ε + 3 * (H s : ℝ) / W
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbound (n : ℕ) (_hn : n ∈ range (N s)) : windowFourierNorm r n W ≤ 1 :=
    windowFourierNorm_le_one r (stitched_residual_abs_le_one N hN m hF) n W hW
  have hgood (n : ℕ) (hn : n ∈ range (N s)) (hgood : n ∉ E) : windowFourierNorm r n W ≤ A := by
    have hgood' : ¬ (n < N (s - 1) ∨ N s ≤ n + W) := by
      intro h
      exact hgood (mem_filter.mpr ⟨hn, h⟩)
    have heq (i : ℕ) (hi : i < W) : r (n + i) = F (n + i) - (m s).value (n + i) := by
      change F (n + i) - (m (firstCutIndex N hN (n + i))).value (n + i) = _
      rw [firstCutIndex_eq N hN hmono s (n + i) (by omega) (by omega)]
    rw [windowFourierNorm_congr r (fun k => F k - (m s).value k) n W heq]
    apply windowFourierNorm_of_blocks _ ((m s).residual_abs_le_one hF) (H s) n W hH hW ε hε0 hε1
    intro b β
    simpa only [Finset.sum_range] using (m s).fourier_bound b β
  have havg := exceptional_average_bound (fun n => windowFourierNorm r n W)
    (N s) hNs E A hA hbound hgood
  have hcard : (E.card : ℝ) ≤ (N (s - 1) : ℝ) + W := by
    exact_mod_cast edge_window_count (N s) (N (s - 1)) W
  exact havg.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg (N s))))

theorem stitched_residual_fourier_average_asymptotic
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (m : ∀ s, BlockRegularModel F (H s) L ε)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (W : ℕ → ℕ)
    (hH : ∀ᶠ s in atTop, 0 < H s) (hW : ∀ᶠ s in atTop, 0 < W s)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (hHW : Tendsto (fun s => (H s : ℝ) / W s) atTop (𝓝 0))
    (hWN : Tendsto (fun s => (W s : ℝ) / N s) atTop (𝓝 0)) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ s in atTop,
      (∑ n ∈ range (N s), windowFourierNorm (fun k => F k - stitchedBlockValue N hN m k) n (W s)) / N s ≤
        ε + e s := by
  refine ⟨fun s => 3 * ((H s : ℝ) / W s) + (N (s - 1) : ℝ) / N s + (W s : ℝ) / N s, ?_, ?_⟩
  · simpa only [mul_zero, add_zero] using ((hHW.const_mul 3).add hprev).add hWN
  · filter_upwards [hH, hW, hN.eventually (eventually_gt_atTop 0)] with s hs ht hu
    have hb := stitched_residual_fourier_average_bound N hN hmono m hF hε0 hε1 s (W s) hs ht hu
    calc
      _ ≤ ε + 3 * (H s : ℝ) / W s + ((N (s - 1) : ℝ) + W s) / N s := hb
      _ = _ := by ring

end Erdos335.IntermediateScale
