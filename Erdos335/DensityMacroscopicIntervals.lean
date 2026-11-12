import Erdos335.BlockCounting
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Ordinary density on macroscopic intervals

Privately checked supporting development.
The interval quantity is expressed as a difference of half-open prefix counts.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335

theorem HasDensity.prefixCount_floor_real_tendsto
    {S : Set ℕ} {ρ : ℝ} (hS : HasDensity S ρ)
    {ι : Type*} {L : Filter ι} (H : ι → ℝ) (hH : Tendsto H L atTop)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun i => (prefixCount S (Nat.floor (t * H i)) : ℝ) / H i)
      L (𝓝 (ρ * t)) := by
  classical
  by_cases ht0 : t = 0
  · simpa [ht0, prefixCount] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) L (𝓝 0))
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let N : ι → ℕ := fun i => Nat.floor (t * H i)
  have hN_top : Tendsto N L atTop :=
    tendsto_nat_floor_atTop.comp (Tendsto.const_mul_atTop htpos hH)
  have hdensity : Tendsto
      (fun i => (prefixCount S (N i) : ℝ) / (N i : ℝ)) L (𝓝 ρ) :=
    ((hasDensity_iff_prefixCount S ρ).mp hS).comp hN_top
  have hscale : Tendsto (fun i => (N i : ℝ) / H i) L (𝓝 t) := by
    simpa only [N, Function.comp_def] using
      (tendsto_nat_floor_mul_div_atTop ht).comp hH
  have hproduct : Tendsto
      (fun i => ((prefixCount S (N i) : ℝ) / (N i : ℝ)) *
        ((N i : ℝ) / H i)) L (𝓝 (ρ * t)) := hdensity.mul hscale
  have hcancel :
      (fun i => ((prefixCount S (N i) : ℝ) / (N i : ℝ)) *
        ((N i : ℝ) / H i)) =ᶠ[L]
        (fun i => (prefixCount S (Nat.floor (t * H i)) : ℝ) / H i) := by
    filter_upwards [hN_top.eventually (eventually_ge_atTop 1)] with i hi
    have hNr : (N i : ℝ) ≠ 0 := by
      exact_mod_cast (show N i ≠ 0 by omega)
    exact div_mul_div_cancel₀ hNr
  exact (tendsto_congr' hcancel).mp hproduct

/-- The numerator counts `S` in the half-open interval between the two floors. -/
theorem HasDensity.macroscopic_interval_real_tendsto
    {S : Set ℕ} {ρ : ℝ} (hS : HasDensity S ρ)
    {ι : Type*} {L : Filter ι} (H : ι → ℝ) (hH : Tendsto H L atTop)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    Tendsto (fun i =>
      ((prefixCount S (Nat.floor (v * H i)) : ℝ) -
        (prefixCount S (Nat.floor (u * H i)) : ℝ)) / H i)
      L (𝓝 (ρ * (v - u))) := by
  have hv := hS.prefixCount_floor_real_tendsto H hH v (hu.trans huv)
  have hu' := hS.prefixCount_floor_real_tendsto H hH u hu
  simpa only [sub_div, mul_sub] using hv.sub hu'

theorem HasDensity.prefixCount_floor_pnat_tendsto
    {S : Set ℕ} {ρ : ℝ} (hS : HasDensity S ρ)
    (q : ℕ → ℕ+) (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n =>
      (prefixCount S (Nat.floor (t * ((q n : ℕ) : ℝ))) : ℝ) /
        ((q n : ℕ) : ℝ)) atTop (𝓝 (ρ * t)) := by
  have hqR : Tendsto (fun n => ((q n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  exact hS.prefixCount_floor_real_tendsto (fun n => ((q n : ℕ) : ℝ)) hqR t ht

theorem HasDensity.macroscopic_interval_pnat_tendsto
    {S : Set ℕ} {ρ : ℝ} (hS : HasDensity S ρ)
    (q : ℕ → ℕ+) (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    Tendsto (fun n =>
      ((prefixCount S (Nat.floor (v * ((q n : ℕ) : ℝ))) : ℝ) -
        (prefixCount S (Nat.floor (u * ((q n : ℕ) : ℝ))) : ℝ)) /
        ((q n : ℕ) : ℝ)) atTop (𝓝 (ρ * (v - u))) := by
  have hqR : Tendsto (fun n => ((q n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  exact hS.macroscopic_interval_real_tendsto
    (fun n => ((q n : ℕ) : ℝ)) hqR u v hu huv

end Erdos335
