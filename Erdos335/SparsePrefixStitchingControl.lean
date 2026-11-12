import Erdos335.PrefixBlockStitching
import Erdos335.PrefixCorrelationContinuity
import Erdos335.PrefixMeanContinuity

/-!
# Preservation of orthogonality under sparse-prefix stitching
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem tendsto_zero_of_square_bound (u v : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (hbound : ∀ᶠ s in atTop, u s ^ 2 ≤ v s) :
    Tendsto u atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hbound, hv.eventually (eventually_lt_nhds (sq_pos_of_pos hε))] with s hs hv'
  rw [Real.dist_eq, sub_zero]
  apply abs_lt.mpr
  constructor <;> nlinarith

theorem sparse_prefix_stitch_energy (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (f : ℕ → ℕ → ℝ) (hf : ∀ s n, f s n ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun s => prefixEnergy (fun n => prefixStitch N hN f id n - f s n) (N s))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun s => prefixEnergy_nonneg _ _) ?_ hratio
  apply Eventually.of_forall
  intro s
  have h := prefixStitch_energy_bound N hN hmono f hf id s s
  simp only [id_eq, sub_self, zero_pow (by decide : 2 ≠ 0), sum_const_zero, add_zero] at h
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg (N s) : (0 : ℝ) ≤ N s)

theorem sparse_prefix_stitch_orthogonality (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (F : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ s n, f s n ∈ Set.Icc (0 : ℝ) 1)
    (horth : Tendsto (fun s => prefixCorrelation (f s) (fun n => F n - f s n) (N s))
      atTop (𝓝 0)) :
    Tendsto (fun s => prefixCorrelation (prefixStitch N hN f id)
      (fun n => F n - prefixStitch N hN f id n) (N s)) atTop (𝓝 0) := by
  let g := prefixStitch N hN f id
  have hg : ∀ n, g n ∈ Set.Icc (0 : ℝ) 1 := prefixStitch_bounds N hN f hf id
  have henergy := sparse_prefix_stitch_energy N hN hmono hratio f hf
  have hscaled : Tendsto (fun s => 4 * prefixEnergy (fun n => g n - f s n) (N s)) atTop (𝓝 0) := by
    simpa only [mul_zero] using henergy.const_mul 4
  have hdiff := tendsto_zero_of_square_bound
    (fun s => prefixCorrelation g (fun n => F n - g n) (N s) -
      prefixCorrelation (f s) (fun n => F n - f s n) (N s))
    (fun s => 4 * prefixEnergy (fun n => g n - f s n) (N s)) hscaled
    (Eventually.of_forall fun s => prefix_orthogonality_difference_sq_le F g (f s) hF hg (hf s) (N s))
  have h := hdiff.add horth
  simp only [sub_add_cancel, add_zero] at h
  exact h

theorem sparse_prefix_stitch_mean (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (F : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ s n, f s n ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun s => prefixCorrelation (fun n => F n - f s n) (fun _ => 1) (N s))
      atTop (𝓝 0)) :
    Tendsto (fun s => prefixCorrelation (fun n => F n - prefixStitch N hN f id n)
      (fun _ => 1) (N s)) atTop (𝓝 0) := by
  let g := prefixStitch N hN f id
  have henergy := sparse_prefix_stitch_energy N hN hmono hratio f hf
  have hdiff := tendsto_zero_of_square_bound
    (fun s => prefixCorrelation (fun n => g n - f s n) (fun _ => 1) (N s))
    (fun s => prefixEnergy (fun n => g n - f s n) (N s)) henergy
    (Eventually.of_forall fun s => prefix_mean_sq_le_energy _ _)
  have h := hmean.sub hdiff
  simp only [sub_zero] at h
  apply h.congr
  intro s
  simp only [prefixCorrelation, mul_one, sum_sub_distrib]
  ring

end Erdos335.IntermediateScale
