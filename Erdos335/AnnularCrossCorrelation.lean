import Erdos335.BlockModelCorrelation
import Erdos335.AnnularBlockModels
import Erdos335.SparseCrossCorrelation

/-!
# Asymptotic correlations of stitched arithmetic regularity models
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem stitched_models_correlation_bound
    {F : ℕ → ℝ} {Hfine Hcoarse : ℕ → ℕ} {L K : ℕ} {ε η : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (m : ∀ s, BlockRegularModel F (Hcoarse s) L ε)
    (r : ∀ s, BlockRegularModel F (Hfine s) K η)
    (hcoarse : ∀ s, 0 < Hcoarse s) (hfine : ∀ s, 0 < Hfine s)
    (hε : 0 ≤ ε) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hscale : Hfine = Hcoarse ∨
      Tendsto (fun s => (Hfine s : ℝ) / Hcoarse s) atTop (𝓝 0))
    (hcoarseN : Tendsto (fun s => (Hcoarse s : ℝ) / N s) atTop (𝓝 0)) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ s in atTop,
      |prefixCorrelation (stitchedBlockValue N hN m)
        (fun n => F n - stitchedBlockValue N hN r n) (N s)| ≤ ε + L * η + e s := by
  let a := fun s => prefixCorrelation (stitchedBlockValue N hN m)
    (fun n => F n - stitchedBlockValue N hN r n) (N s)
  let b := fun s => prefixCorrelation (m s).value (fun n => F n - (r s).value n) (N s)
  have hpatch : Tendsto (fun s => |a s - b s|) atTop (𝓝 0) := by
    simpa only [a, b, stitchedBlockValue, Real.norm_eq_abs, abs_zero] using
      (sparse_stitch_cross_correlation N hN hmono hprev F
        (fun s => (m s).value) (fun s => (r s).value) hF
        (fun s => (m s).value_mem) (fun s => (r s).value_mem)).abs
  have htriangle (s : ℕ) : |a s| ≤ |a s - b s| + |b s| := by
    have h := norm_add_le (a s - b s) (b s)
    simpa only [sub_add_cancel, Real.norm_eq_abs] using h
  rcases hscale with heq | hratio
  · subst Hfine
    refine ⟨fun s => |a s - b s| + (Hcoarse s : ℝ) / N s,
      by simpa only [add_zero] using hpatch.add hcoarseN, ?_⟩
    filter_upwards [hN.eventually (eventually_gt_atTop 0)] with s hs
    have hb := (m s).same_scale_prefix_correlation (r s) hF (hcoarse s) hε hη0 (N s) hs
    change |a s| ≤ _
    change |b s| ≤ ε + L * η + (Hcoarse s : ℝ) / N s at hb
    linarith [htriangle s]
  · let d := fun s => (L : ℝ) * (3 * ((Hfine s : ℝ) / Hcoarse s)) + (Hcoarse s : ℝ) / N s
    have hd : Tendsto d atTop (𝓝 0) := by
      simpa only [d, mul_zero, add_zero] using ((hratio.const_mul 3).const_mul (L : ℝ)).add hcoarseN
    refine ⟨fun s => |a s - b s| + d s, by simpa only [add_zero] using hpatch.add hd, ?_⟩
    filter_upwards [hN.eventually (eventually_gt_atTop 0)] with s hs
    have hb := (m s).cross_scale_prefix_correlation (r s) hF (hcoarse s) (hfine s)
      hε hη0 hη1 (N s) hs
    have hb' : |b s| ≤ ε + L * η + d s := by
      calc
        _ ≤ ε + L * (η + 3 * (Hfine s : ℝ) / Hcoarse s) + (Hcoarse s : ℝ) / N s := hb
        _ = _ := by dsimp [d]; ring
    change |a s| ≤ _
    linarith [htriangle s]

end Erdos335.IntermediateScale
