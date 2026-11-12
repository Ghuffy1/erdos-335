import Erdos335.FiniteRegularityParameters
import Erdos335.CircleCellPolynomials

/-!
# Parameters for uniform finite character regularity
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_continuous_model_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ (τ : ℝ) (N D M : ℕ), 0 < τ ∧ 2 * τ ≤ ε ∧ 2 ≤ N ∧ 0 < M ∧
      1 / (N : ℝ) ≤ τ / 2 ∧
      1 < (D : ℝ) * (τ / 2 - 1 / (N : ℝ)) ^ 2 ∧
      (D : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ D + 1) ^ 2 ≤ (ε / 2) ^ 2 * M := by
  let τ := min ε 1 / 2
  have hτ : 0 < τ := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hτε : 2 * τ ≤ ε := by dsimp [τ]; linarith [min_le_left ε 1]
  have hτ1 : τ ≤ 1 / 2 := by dsimp [τ]; linarith [min_le_right ε 1]
  obtain ⟨N, D, hN, hsmall, hD⟩ := exists_finite_regularity_parameters (τ / 2) (by positivity)
  have hN2 : 2 ≤ N := by
    by_contra hn
    have heq : N = 1 := by omega
    subst N
    norm_num at hsmall
    linarith
  let A : ℝ := (D : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ D + 1) ^ 2
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (A / (ε / 2) ^ 2))
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hM)
    exact_mod_cast this
  refine ⟨τ, N, D, M, hτ, hτε, hN2, hMpos, ?_, hD, ?_⟩
  · exact hsmall.trans (by linarith)
  · have hδ : (0 : ℝ) < (ε / 2) ^ 2 := sq_pos_of_pos (by positivity)
    have hbound := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hM)
    change A ≤ (ε / 2) ^ 2 * M
    linarith

theorem exists_cell_polynomial_parameters (N M D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (K : ℕ) (η : ℝ)
      (T : (Bool × Fin M × Fin (2 * N + 1)) → Finset ℤ)
      (w : (Bool × Fin M × Fin (2 * N + 1)) → ℤ → ℂ),
      0 < K ∧ 0 < η ∧ η ≤ 1 ∧
      ((2 * N + 1 : ℕ) : ℝ) ^ D * (D * η * 2 ^ D) ≤ δ ∧
      (∀ tag, (T tag).card ≤ K) ∧
      (∀ tag n, n ∈ T tag → ‖w tag n‖ ≤ K) ∧
      ∀ tag z, ‖circleCell N M tag z - ∑ n ∈ T tag, w tag n * (z : ℂ) ^ n‖ ≤ η := by
  let B : ℝ := ((2 * N + 1 : ℕ) : ℝ) ^ D * (D + 1) * 2 ^ D
  have hB : 0 < B := by dsimp [B]; positivity
  let η := min 1 (δ / B)
  have hη : 0 < η := lt_min zero_lt_one (div_pos hδ hB)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηB : η * B ≤ δ := (le_div_iff₀ hB).mp (min_le_right _ _)
  have hE : ((2 * N + 1 : ℕ) : ℝ) ^ D * (D * η * 2 ^ D) ≤ δ := by
    calc
      _ ≤ ((2 * N + 1 : ℕ) : ℝ) ^ D * ((D + 1) * η * 2 ^ D) := by gcongr; linarith
      _ = η * B := by dsimp [B]; ring
      _ ≤ δ := hηB
  obtain ⟨K, T, w, hK, hT, hw, happrox⟩ := uniform_circleCell_polynomials N M η hη
  exact ⟨K, η, T, w, hK, hη, hη1, hE, hT,
    fun tag n hn => (hw tag n hn).2, fun tag z => (happrox tag z).le⟩

end Erdos335.IntermediateScale
