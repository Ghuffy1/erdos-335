import Erdos335.BlockArithmeticRegularity
import Erdos335.BlockModelPrefixControl
import Erdos335.PrefixEnergyAlgebra

/-!
# Data and estimates for a block arithmetic regularity model
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

structure BlockRegularModel (F : ℕ → ℝ) (H L : ℕ) (ε : ℝ) where
  value : ℕ → ℝ
  frequency : ℕ → Fin L → ℝ
  coefficient : ℕ → Fin L → ℂ
  value_mem : ∀ n, value n ∈ Set.Icc (0 : ℝ) 1
  coefficient_bound : ∀ b j, ‖coefficient b j‖ ≤ 1
  zero_mean : ∀ b, (∑ i : Fin H, (F (H * b + i.val) - value (H * b + i.val))) = 0
  orthogonal : ∀ b, (∑ i : Fin H, value (H * b + i.val) *
    (F (H * b + i.val) - value (H * b + i.val))) = 0
  fourier_bound : ∀ b β, ‖∑ i : Fin H,
    ((F (H * b + i.val) - value (H * b + i.val) : ℝ) : ℂ) *
      unitCharacter (((H * b + i.val : ℕ) : ℝ) * β)‖ ≤ ε * H
  approximation : ∀ b,
    (∑ i : Fin H, ‖(value (H * b + i.val) : ℂ) -
      ∑ j, coefficient b j * unitCharacter (((H * b + i.val : ℕ) : ℝ) * frequency b j)‖ ^ 2) / H ≤ ε ^ 2

theorem exists_block_regular_model (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ (H : ℕ), 0 < H → ∀ F : ℕ → ℝ,
      (∀ n, F n ∈ Set.Icc (0 : ℝ) 1) → Nonempty (BlockRegularModel F H L ε) := by
  obtain ⟨L, hL, hmodels⟩ := blockwise_arithmetic_regularity ε hε
  refine ⟨L, hL, fun H hH F hF => ?_⟩
  obtain ⟨g, α, a, hg, ha, hb⟩ := hmodels H hH F hF
  exact ⟨⟨g, α, a, hg, ha, fun b => (hb b).1, fun b => (hb b).2.1,
    fun b => (hb b).2.2.1, fun b => (hb b).2.2.2⟩⟩

noncomputable def BlockRegularModel.polynomial {F : ℕ → ℝ} {H L : ℕ} {ε : ℝ}
    (m : BlockRegularModel F H L ε) (n : ℕ) : ℂ :=
  ∑ j, m.coefficient (n / H) j * unitCharacter ((n : ℝ) * m.frequency (n / H) j)

theorem BlockRegularModel.polynomial_norm_le {F : ℕ → ℝ} {H L : ℕ} {ε : ℝ}
    (m : BlockRegularModel F H L ε) (n : ℕ) : ‖m.polynomial n‖ ≤ L :=
  real_frequency_polynomial_norm_le _ _ _ (m.coefficient_bound (n / H))

theorem BlockRegularModel.error_sq_bound {F : ℕ → ℝ} {H L : ℕ} {ε : ℝ}
    (m : BlockRegularModel F H L ε) (n : ℕ) :
    ‖(m.value n : ℂ) - m.polynomial n‖ ^ 2 ∈ Set.Icc (0 : ℝ) (((L : ℝ) + 1) ^ 2) := by
  refine ⟨sq_nonneg _, ?_⟩
  have hvalue : ‖(m.value n : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (m.value_mem n).1]
      using (m.value_mem n).2
  have hbound := (norm_sub_le (m.value n : ℂ) (m.polynomial n)).trans
    (add_le_add hvalue (m.polynomial_norm_le n))
  nlinarith [norm_nonneg ((m.value n : ℂ) - m.polynomial n)]

theorem BlockRegularModel.prefix_approximation {F : ℕ → ℝ} {H L : ℕ} {ε : ℝ}
    (m : BlockRegularModel F H L ε) (hH : 0 < H) (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ range N, ‖(m.value n : ℂ) - m.polynomial n‖ ^ 2) / N ≤
      ε ^ 2 + ((L : ℝ) + 1) ^ 2 * H / N := by
  apply prefix_polynomial_model_error m.value m.polynomial m.value_mem L m.polynomial_norm_le H N hH hN ε
  intro b
  have hbound := (div_le_iff₀ (show (0 : ℝ) < H by exact_mod_cast hH)).mp (m.approximation b)
  have hpoly (i : Fin H) : m.polynomial (H * b + i.val) =
      ∑ j, m.coefficient b j * unitCharacter (((H * b + i.val : ℕ) : ℝ) * m.frequency b j) := by
    unfold BlockRegularModel.polynomial
    rw [Nat.mul_add_div hH, Nat.div_eq_of_lt i.isLt, add_zero]
  simpa only [Finset.sum_range, hpoly] using hbound

theorem BlockRegularModel.residual_abs_le_one {F : ℕ → ℝ} {H L : ℕ} {ε : ℝ}
    (m : BlockRegularModel F H L ε) (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    |F n - m.value n| ≤ 1 := by
  apply abs_le.mpr
  constructor <;> linarith [(hF n).1, (hF n).2, (m.value_mem n).1, (m.value_mem n).2]

theorem BlockRegularModel.prefix_mean {F : ℕ → ℝ} {H L : ℕ} {ε : ℝ}
    (m : BlockRegularModel F H L ε) (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hH : 0 < H) (N : ℕ) :
    |prefixCorrelation (fun n => F n - m.value n) (fun _ => 1) N| ≤ (H : ℝ) / N := by
  simp only [prefixCorrelation, mul_one]
  apply prefix_zero_block_real_average _ (m.residual_abs_le_one hF) H N hH
  intro b
  simpa only [Finset.sum_range] using m.zero_mean b

theorem BlockRegularModel.prefix_orthogonality {F : ℕ → ℝ} {H L : ℕ} {ε : ℝ}
    (m : BlockRegularModel F H L ε) (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hH : 0 < H) (N : ℕ) :
    |prefixCorrelation m.value (fun n => F n - m.value n) N| ≤ (H : ℝ) / N := by
  have hbound (n : ℕ) : |m.value n * (F n - m.value n)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (m.value_mem n).1]
    exact (mul_le_mul (m.value_mem n).2 (m.residual_abs_le_one hF n) (abs_nonneg _) zero_le_one).trans
      (by norm_num)
  have hzero (b : ℕ) : (∑ i ∈ range H, m.value (H * b + i) *
      (F (H * b + i) - m.value (H * b + i))) = 0 := by
    simpa only [Finset.sum_range] using m.orthogonal b
  exact prefix_zero_block_real_average _ hbound H N hH hzero

end Erdos335.IntermediateScale
