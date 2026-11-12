import Erdos335.PrefixEnergyAlgebra
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp

/-!
# Continuity of bounded orthogonality expressions in prefix mean square
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_orthogonality_difference_sq_le
    (F g h : ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ n, g n ∈ Set.Icc (0 : ℝ) 1)
    (hh : ∀ n, h n ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    (prefixCorrelation g (fun n => F n - g n) N -
      prefixCorrelation h (fun n => F n - h n) N) ^ 2 ≤
        4 * prefixEnergy (fun n => g n - h n) N := by
  by_cases hN : N = 0
  · simp [prefixCorrelation, prefixEnergy, hN]
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  let d := fun n => g n * (F n - g n) - h n * (F n - h n)
  have hd (n : ℕ) : d n ^ 2 ≤ 4 * (g n - h n) ^ 2 := by
    have hfactor : d n = (g n - h n) * (F n - g n - h n) := by dsimp [d]; ring
    have hlow : 0 ≤ 2 + (F n - g n - h n) := by linarith [(hF n).1, (hg n).2, (hh n).2]
    have hhigh : 0 ≤ 2 - (F n - g n - h n) := by linarith [(hF n).2, (hg n).1, (hh n).1]
    have hsq : (F n - g n - h n) ^ 2 ≤ 4 := by nlinarith [mul_nonneg hlow hhigh]
    rw [hfactor, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (g n - h n))]
  have hcs := sum_mul_sq_le_sq_mul_sq (range N) d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_range, nsmul_eq_mul] at hcs
  have hsum := sum_le_sum (fun n (_ : n ∈ range N) => hd n)
  rw [← mul_sum] at hsum
  have heq : prefixCorrelation g (fun n => F n - g n) N -
      prefixCorrelation h (fun n => F n - h n) N = (∑ n ∈ range N, d n) / N := by
    simp only [prefixCorrelation, sub_div, sum_sub_distrib, d]
  rw [heq, div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).mpr
  calc
    _ ≤ (∑ n ∈ range N, d n ^ 2) * N := hcs
    _ ≤ (4 * ∑ n ∈ range N, (g n - h n) ^ 2) * N :=
      mul_le_mul_of_nonneg_right hsum hNr.le
    _ = (4 * prefixEnergy (fun n => g n - h n) N) * (N : ℝ) ^ 2 := by
      unfold prefixEnergy
      field_simp

theorem prefix_orthogonality_limit
    (N : ℕ → ℕ) (F g : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ n, g n ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (happrox : ∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
      prefixEnergy (fun n => g n - f k n) (N s) ≤ δ)
    (horth : ∀ k, Tendsto (fun s => prefixCorrelation (f k) (fun n => F n - f k n) (N s))
      atTop (𝓝 0)) :
    Tendsto (fun s => prefixCorrelation g (fun n => F n - g n) (N s)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := happrox (ε ^ 2 / 16) (by positivity)
  have hsmall := (horth K).eventually (Metric.ball_mem_nhds (0 : ℝ) (show 0 < ε / 2 by positivity))
  filter_upwards [hK K le_rfl, hsmall] with s hs hks
  have hsq := prefix_orthogonality_difference_sq_le F g (f K) hF hg (hf K) (N s)
  have habs : |prefixCorrelation g (fun n => F n - g n) (N s) -
      prefixCorrelation (f K) (fun n => F n - f K n) (N s)| ≤ ε / 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hkabs : |prefixCorrelation (f K) (fun n => F n - f K n) (N s)| < ε / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hks
  rw [Real.dist_eq, sub_zero]
  have hdiff := abs_le.mp habs
  have hnear := abs_lt.mp hkabs
  exact abs_lt.mpr ⟨by linarith [hdiff.1, hnear.1], by linarith [hdiff.2, hnear.2]⟩

end Erdos335.IntermediateScale
