import Erdos335.BlockRegularModel
import Erdos335.CrossScaleBlockCorrelation

/-!
# Correlations between arithmetic regularity models
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem BlockRegularModel.same_scale_block_correlation
    {F : ℕ → ℝ} {H L K : ℕ} {ε η : ℝ}
    (m : BlockRegularModel F H L ε) (r : BlockRegularModel F H K η)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1) (hH : 0 < H) (hε : 0 ≤ ε) (b : ℕ) :
    |∑ i ∈ range H, m.value (H * b + i) * (F (H * b + i) - r.value (H * b + i))| ≤
      (ε + L * η) * H := by
  letI : NeZero H := ⟨hH.ne'⟩
  have h := finite_polynomial_correlation_bound
    (fun i : Fin H => m.value (H * b + i.val))
    (fun i : Fin H => F (H * b + i.val) - r.value (H * b + i.val))
    (fun j (i : Fin H) => unitCharacter (((H * b + i.val : ℕ) : ℝ) * m.frequency b j))
    (m.coefficient b) ε η hε (fun i => r.residual_abs_le_one hF _)
    (m.coefficient_bound b)
    (by simpa only [Fintype.card_fin] using m.approximation b)
    (fun j => by simpa only [Fintype.card_fin] using r.fourier_bound b (m.frequency b j))
  simpa only [Finset.sum_range, Fintype.card_fin] using h

theorem BlockRegularModel.same_scale_prefix_correlation
    {F : ℕ → ℝ} {H L K : ℕ} {ε η : ℝ}
    (m : BlockRegularModel F H L ε) (r : BlockRegularModel F H K η)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1) (hH : 0 < H)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (N : ℕ) (hN : 0 < N) :
    |prefixCorrelation m.value (fun n => F n - r.value n) N| ≤
      ε + L * η + (H : ℝ) / N := by
  let A := ε + L * η
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hn (n : ℕ) : ‖((m.value n * (F n - r.value n) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (m.value_mem n).1]
    exact (mul_le_mul (m.value_mem n).2 (r.residual_abs_le_one hF n)
      (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hb (b : ℕ) :
      ‖∑ i ∈ range H, ((m.value (H * b + i) * (F (H * b + i) - r.value (H * b + i)) : ℝ) : ℂ)‖ ≤ A * H := by
    simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
      using m.same_scale_block_correlation r hF hH hε b
  have hbound := prefix_norm_bound_of_block_norm_bound
    (fun n => ((m.value n * (F n - r.value n) : ℝ) : ℂ)) hn H N hH A hA hb
  have hreal : |∑ n ∈ range N, m.value n * (F n - r.value n)| ≤ A * N + H := by
    simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using hbound
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [prefixCorrelation, abs_div, abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  have heq : (A + (H : ℝ) / N) * N = A * N + H := by field_simp
  change |∑ n ∈ range N, m.value n * (F n - r.value n)| ≤ (A + (H : ℝ) / N) * N
  rw [heq]
  exact hreal

theorem BlockRegularModel.cross_scale_prefix_correlation
    {F : ℕ → ℝ} {Hcoarse Hfine L K : ℕ} {ε η : ℝ}
    (m : BlockRegularModel F Hcoarse L ε) (r : BlockRegularModel F Hfine K η)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1) (hcoarse : 0 < Hcoarse) (hfine : 0 < Hfine)
    (hε : 0 ≤ ε) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (N : ℕ) (hN : 0 < N) :
    |prefixCorrelation m.value (fun n => F n - r.value n) N| ≤
      ε + L * (η + 3 * (Hfine : ℝ) / Hcoarse) + (Hcoarse : ℝ) / N := by
  apply cross_scale_prefix_correlation_bound m.value (fun n => F n - r.value n)
    m.value_mem (r.residual_abs_le_one hF) Hfine Hcoarse L N hfine hcoarse hN
    ε η hε hη0 hη1 m.coefficient m.frequency m.coefficient_bound m.approximation
  intro b β
  simpa only [Finset.sum_range] using r.fourier_bound b β

end Erdos335.IntermediateScale
