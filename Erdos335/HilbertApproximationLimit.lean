import Erdos335.AlmostMonotoneEnergy
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

/-!
# Hilbert limits of bounded approximately nested structured components
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace

namespace Erdos335.IntermediateScale

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hilbert_approximation_distance_identity (f : E) (u : ℕ → E)
    (hown : ∀ k, ⟪u k, f - u k⟫_ℝ = 0) (k l : ℕ) :
    ‖u l - u k‖ ^ 2 = ‖u l‖ ^ 2 - ‖u k‖ ^ 2 + 2 * ⟪u k, f - u l⟫_ℝ := by
  have hk := hown k
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hk
  rw [norm_sub_sq_real, real_inner_comm (u k) (u l), inner_sub_right]
  linarith

theorem hilbert_approximation_energy_cauchy (f : E) (u : ℕ → E)
    (hu : ∀ k, ‖u k‖ ≤ 1) (hown : ∀ k, ⟪u k, f - u k⟫_ℝ = 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |⟪u k, f - u l⟫_ℝ| ≤ ε k) :
    CauchySeq (fun k => ‖u k‖ ^ 2) := by
  apply cauchy_of_almost_monotone (fun k => ‖u k‖ ^ 2) (fun k => 2 * ε k)
  · refine ⟨1, ?_⟩
    rintro x ⟨k, rfl⟩
    nlinarith [hu k, norm_nonneg (u k)]
  · simpa only [mul_zero] using hε.const_mul 2
  · intro k l hkl
    have hid := hilbert_approximation_distance_identity f u hown k l
    have hb := (le_abs_self _).trans (hcross k l hkl)
    nlinarith [sq_nonneg ‖u l - u k‖]

theorem hilbert_approximation_cauchy (f : E) (u : ℕ → E)
    (hu : ∀ k, ‖u k‖ ≤ 1) (hown : ∀ k, ⟪u k, f - u k⟫_ℝ = 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |⟪u k, f - u l⟫_ℝ| ≤ ε k) : CauchySeq u := by
  obtain ⟨b, _, hb, hblim⟩ := cauchySeq_iff_le_tendsto_0.mp
    (hilbert_approximation_energy_cauchy f u hu hown ε hε hcross)
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  have hquarter : (0 : ℝ) < δ ^ 2 / 4 := by positivity
  have heighth : (0 : ℝ) < δ ^ 2 / 8 := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((hblim.eventually (eventually_lt_nhds hquarter)).and (hε.eventually (eventually_lt_nhds heighth)))
  have hforward (k l : ℕ) (hk : K ≤ k) (hkl : k ≤ l) : dist (u k) (u l) < δ := by
    have henergy : ‖u l‖ ^ 2 - ‖u k‖ ^ 2 ≤ b k := by
      apply (le_abs_self _).trans
      simpa only [Real.dist_eq] using hb l k k hkl le_rfl
    have hinner := (le_abs_self _).trans (hcross k l hkl)
    have hid : dist (u k) (u l) ^ 2 = ‖u l‖ ^ 2 - ‖u k‖ ^ 2 + 2 * ⟪u k, f - u l⟫_ℝ := by
      rw [dist_eq_norm, norm_sub_rev, hilbert_approximation_distance_identity f u hown]
    have hsmall := hK k hk
    nlinarith [dist_nonneg (x := u k) (y := u l)]
  refine ⟨K, fun k hk l hl => ?_⟩
  rcases le_total k l with hkl | hlk
  · exact hforward k l hk hkl
  · simpa only [dist_comm] using hforward l k hl hlk

theorem exists_hilbert_approximation_limit [CompleteSpace E] (f : E) (u : ℕ → E)
    (hu : ∀ k, ‖u k‖ ≤ 1) (hown : ∀ k, ⟪u k, f - u k⟫_ℝ = 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |⟪u k, f - u l⟫_ℝ| ≤ ε k) :
    ∃ g : E, Tendsto u atTop (𝓝 g) ∧ ‖g‖ ≤ 1 ∧ ⟪g, f - g⟫_ℝ = 0 := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (hilbert_approximation_cauchy f u hu hown ε hε hcross)
  refine ⟨g, hg, le_of_tendsto' hg.norm hu, ?_⟩
  have hinner : Tendsto (fun k => ⟪u k, f - u k⟫_ℝ) atTop (𝓝 ⟪g, f - g⟫_ℝ) :=
    Filter.Tendsto.inner (𝕜 := ℝ) hg (tendsto_const_nhds.sub hg)
  have hzero : Tendsto (fun k => ⟪u k, f - u k⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hown] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hinner hzero

end Erdos335.IntermediateScale
