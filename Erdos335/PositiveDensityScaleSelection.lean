import Erdos335.PositiveDensityMultiplicativeGaps
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Selecting positive-density points at a prescribed real scale

Privately checked supporting development.
The selector is the next point of `A` after the natural floor of `t * H i`.
Natural floor gives a defined selector even when an initial scale is negative.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335

theorem exists_positive_density_scale_selection
    {ι : Type*} (L : Filter ι)
    (A : Set ℕ) (a : ℝ) (hA : HasDensity A a) (ha : 0 < a)
    (H : ι → ℝ) (hH : Tendsto H L atTop) (t : ℝ) (ht : 0 < t) :
    ∃ s : ι → ℕ,
      (∀ i, s i ∈ A) ∧
      (∀ i, Nat.floor (t * H i) < s i) ∧
      Tendsto (fun i => (s i : ℝ) / H i) L (𝓝 t) ∧
      (∀ᶠ i in L, 0 < (s i : ℝ) / H i ∧
        |(s i : ℝ) / H i| ≤ t + 1) := by
  classical
  obtain ⟨k, hk, hk_limit⟩ := exists_next_point_ratio_tendsto_one A a hA ha
  let N : ι → ℕ := fun i => Nat.floor (t * H i)
  let s : ι → ℕ := fun i => k (N i)
  have hN_top : Tendsto N L atTop :=
    tendsto_nat_floor_atTop.comp (Tendsto.const_mul_atTop ht hH)
  have hfloor_ratio : Tendsto (fun i => (N i : ℝ) / H i) L (𝓝 t) := by
    simpa only [N, Function.comp_def] using
      (tendsto_nat_floor_mul_div_atTop ht.le).comp hH
  have hnext_ratio : Tendsto (fun i => (s i : ℝ) / (N i : ℝ)) L (𝓝 1) := by
    simpa only [s, Function.comp_def] using hk_limit.comp hN_top
  have hproduct : Tendsto
      (fun i => ((s i : ℝ) / (N i : ℝ)) * ((N i : ℝ) / H i)) L (𝓝 t) := by
    simpa only [one_mul] using hnext_ratio.mul hfloor_ratio
  have hcancel :
      (fun i => ((s i : ℝ) / (N i : ℝ)) * ((N i : ℝ) / H i)) =ᶠ[L]
        (fun i => (s i : ℝ) / H i) := by
    filter_upwards [hN_top.eventually (eventually_ge_atTop 1)] with i hi
    have hNr : (N i : ℝ) ≠ 0 := by
      exact_mod_cast (show N i ≠ 0 by omega)
    exact div_mul_div_cancel₀ hNr
  have hratio : Tendsto (fun i => (s i : ℝ) / H i) L (𝓝 t) :=
    (tendsto_congr' hcancel).mp hproduct
  have hbound : ∀ᶠ i in L, 0 < (s i : ℝ) / H i ∧
      |(s i : ℝ) / H i| ≤ t + 1 := by
    filter_upwards [hratio.eventually (lt_mem_nhds ht),
      hratio.eventually (gt_mem_nhds (show t < t + 1 by linarith))] with i hpos hupper
    refine ⟨hpos, ?_⟩
    rw [abs_of_pos hpos]
    exact hupper.le
  exact ⟨s, (fun i => (hk (N i)).1), (fun i => (hk (N i)).2), hratio, hbound⟩

end Erdos335
