import Erdos335.FiniteProfileConvergence
import Erdos335.NearbyPrefixAverages

/-!
# Finite-valued subsequence limits and ordinary prefix convergence

Private proof development. Verification status is recorded separately. Eventual finite-template approximation follows
by applying the subsequence hypothesis to positive bad cutoffs. Small
successive increments then give convergence by the existing finite-template
stabilization theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Filter Set Topology
open Erdos335.IntermediateScale

noncomputable section

namespace Erdos335

theorem finite_template_close_of_diverging_subsequence_limits
    {X : Type*} [MetricSpace X] (u : ℕ → X) (F : Finset X)
    (hsubseq : ∀ N : ℕ → ℕ, (∀ s, 0 < N s) → Tendsto N atTop atTop →
      ∃ (σ : ℕ → ℕ) (p : X), StrictMono σ ∧ p ∈ F ∧
        Tendsto (fun s => u (N (σ s))) atTop (𝓝 p)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∃ p ∈ F, dist (u n) p < ε := by
  intro ε hε
  by_contra hnot
  have hbad : ∃ᶠ n in atTop, ¬∃ p ∈ F, dist (u n) p < ε :=
    Filter.not_eventually.mp hnot
  obtain ⟨N, hNmono, hNbad⟩ := extraction_of_frequently_atTop
    (hbad.and_eventually (eventually_gt_atTop 0))
  obtain ⟨σ, p, _, hp, hlimit⟩ := hsubseq N (fun s => (hNbad s).2) hNmono.tendsto_atTop
  have hnear : ∀ᶠ s in atTop, dist (u (N (σ s))) p < ε :=
    (Metric.tendsto_nhds.mp hlimit) ε hε
  obtain ⟨s, hs⟩ := hnear.exists
  exact (hNbad (σ s)).1 ⟨p, hp, hs⟩

theorem tendsto_of_finite_diverging_subsequence_limits
    {X : Type*} [MetricSpace X] (u : ℕ → X) (F : Finset X)
    (hsubseq : ∀ N : ℕ → ℕ, (∀ s, 0 < N s) → Tendsto N atTop atTop →
      ∃ (σ : ℕ → ℕ) (p : X), StrictMono σ ∧ p ∈ F ∧
        Tendsto (fun s => u (N (σ s))) atTop (𝓝 p))
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0)) :
    ∃ p ∈ F, Tendsto u atTop (𝓝 p) :=
  tendsto_of_finite_template_approximation u F
    (finite_template_close_of_diverging_subsequence_limits u F hsubseq) hstep

theorem normalized_prefix_step_tendsto_zero
    (T : Set ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n => dist (c * ((prefixCount T (n + 1) : ℝ) / (n + 1 : ℕ)))
      (c * ((prefixCount T n : ℝ) / n))) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      dist (c * ((prefixCount T (n + 1) : ℝ) / (n + 1 : ℕ)))
        (c * ((prefixCount T n : ℝ) / n)) ≤ c / (n + 1 : ℕ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnear := prefix_average_nested_length_error T n (n + 1) hn (Nat.le_succ n)
    calc
      _ = c * |(prefixCount T (n + 1) : ℝ) / (n + 1 : ℕ) -
          (prefixCount T n : ℝ) / n| := by
        rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hc]
      _ ≤ c * (((n + 1 - n : ℕ) : ℝ) / (n + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hnear hc
      _ = c / (n + 1 : ℕ) := by simp [div_eq_mul_inv]
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) hbound
  simpa only [Function.comp_def] using
    (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)

theorem normalized_prefix_limit_of_finite_subsequence_limits
    (T : Set ℕ) (c : ℝ) (hc : 0 ≤ c) (F : Finset ℝ)
    (hsubseq : ∀ N : ℕ → ℕ, (∀ s, 0 < N s) → Tendsto N atTop atTop →
      ∃ (σ : ℕ → ℕ) (p : ℝ), StrictMono σ ∧ p ∈ F ∧
        Tendsto (fun s => c * ((prefixCount T (N (σ s)) : ℝ) / N (σ s)))
          atTop (𝓝 p)) :
    ∃ p ∈ F, Tendsto (fun n => c * ((prefixCount T n : ℝ) / n)) atTop (𝓝 p) :=
  tendsto_of_finite_diverging_subsequence_limits
    (fun n => c * ((prefixCount T n : ℝ) / n)) F hsubseq
      (normalized_prefix_step_tendsto_zero T c hc)

theorem hasDensity_of_normalized_prefix_limit
    (T : Set ℕ) (c v : ℝ) (hc : c ≠ 0)
    (hlimit : Tendsto (fun n => c * ((prefixCount T n : ℝ) / n)) atTop (𝓝 v)) :
    HasDensity T (v / c) := by
  apply (hasDensity_iff_prefixCount T (v / c)).mpr
  have hdiv := hlimit.div_const c
  apply hdiv.congr
  intro n
  simp only [mul_div_cancel_left₀ _ hc]

end Erdos335

end
