import Erdos335.PrefixCorrelationContinuity

/-!
# Passing mean preservation to a prefix mean-square limit
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_mean_sq_le_energy (f : ℕ → ℝ) (N : ℕ) :
    prefixCorrelation f (fun _ => 1) N ^ 2 ≤ prefixEnergy f N := by
  by_cases hN : N = 0
  · simp [prefixCorrelation, prefixEnergy, hN]
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hcs := sum_mul_sq_le_sq_mul_sq (range N) f (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_range, nsmul_eq_mul] at hcs
  simp only [prefixCorrelation, mul_one, div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).mpr
  calc
    _ ≤ (∑ n ∈ range N, f n ^ 2) * N := hcs
    _ = prefixEnergy f N * (N : ℝ) ^ 2 := by unfold prefixEnergy; field_simp

theorem prefix_mean_preservation_limit
    (N : ℕ → ℕ) (F g : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (happrox : ∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
      prefixEnergy (fun n => g n - f k n) (N s) ≤ δ)
    (hmean : ∀ k, Tendsto (fun s => prefixCorrelation (fun n => F n - f k n) (fun _ => 1) (N s))
      atTop (𝓝 0)) :
    Tendsto (fun s => prefixCorrelation (fun n => F n - g n) (fun _ => 1) (N s)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := happrox (ε ^ 2 / 4) (by positivity)
  have hsmall := (hmean K).eventually (Metric.ball_mem_nhds (0 : ℝ) (show 0 < ε / 2 by positivity))
  filter_upwards [hK K le_rfl, hsmall] with s hs hks
  have heq : prefixCorrelation (fun n => F n - g n) (fun _ => 1) (N s) -
      prefixCorrelation (fun n => F n - f K n) (fun _ => 1) (N s) =
        -prefixCorrelation (fun n => g n - f K n) (fun _ => 1) (N s) := by
    simp only [prefixCorrelation, mul_one, sum_sub_distrib]
    ring
  have hsq : (prefixCorrelation (fun n => F n - g n) (fun _ => 1) (N s) -
      prefixCorrelation (fun n => F n - f K n) (fun _ => 1) (N s)) ^ 2 ≤
        prefixEnergy (fun n => g n - f K n) (N s) := by
    rw [heq, neg_sq]
    exact prefix_mean_sq_le_energy _ _
  have habs : |prefixCorrelation (fun n => F n - g n) (fun _ => 1) (N s) -
      prefixCorrelation (fun n => F n - f K n) (fun _ => 1) (N s)| ≤ ε / 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hkabs : |prefixCorrelation (fun n => F n - f K n) (fun _ => 1) (N s)| < ε / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hks
  rw [Real.dist_eq, sub_zero]
  have hdiff := abs_le.mp habs
  have hnear := abs_lt.mp hkabs
  exact abs_lt.mpr ⟨by linarith [hdiff.1, hnear.1], by linarith [hdiff.2, hnear.2]⟩

end Erdos335.IntermediateScale
