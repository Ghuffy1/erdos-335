import Erdos335.BlockFourierTransfer
import Erdos335.FinitePolynomialCorrelation
import Erdos335.PrefixEnergyAlgebra
import Mathlib.Algebra.BigOperators.Fin

/-!
# Correlating a coarse structured model with a finer uniform residual
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_norm_bound_of_block_norm_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (H N : ℕ) (hH : 0 < H) (A : ℝ) (hA : 0 ≤ A)
    (hblock : ∀ b, ‖∑ i ∈ range H, f (H * b + i)‖ ≤ A * H) :
    ‖∑ i ∈ range N, f i‖ ≤ A * N + H := by
  have hrem := prefix_block_remainder_norm f hf H N hH
  have hmain := aligned_blocks_norm_bound f H 0 (N / H) (Nat.zero_le _) A hblock
  simp only [mul_zero, range_zero, sum_empty, sub_zero, Nat.sub_zero] at hmain
  have hlength : ((H * (N / H) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N H
  have hscaled := mul_le_mul_of_nonneg_left hlength hA
  have htriangle := norm_add_le
    ((∑ i ∈ range N, f i) - ∑ i ∈ range (H * (N / H)), f i)
    (∑ i ∈ range (H * (N / H)), f i)
  rw [sub_add_cancel] at htriangle
  push_cast at hscaled
  nlinarith

theorem coarse_block_correlation_bound
    (g r : ℕ → ℝ) (hr : ∀ n, |r n| ≤ 1)
    (Hfine Hcoarse L : ℕ) (hfine : 0 < Hfine) (hcoarse : 0 < Hcoarse)
    (ε η : ℝ) (hε : 0 ≤ ε) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (a : ℕ → Fin L → ℂ) (α : ℕ → Fin L → ℝ)
    (ha : ∀ b j, ‖a b j‖ ≤ 1)
    (happrox : ∀ b,
      (∑ i : Fin Hcoarse, ‖(g (Hcoarse * b + i.val) : ℂ) -
        ∑ j, a b j * unitCharacter (((Hcoarse * b + i.val : ℕ) : ℝ) * α b j)‖ ^ 2) /
          Hcoarse ≤ ε ^ 2)
    (hfrequency : ∀ b β,
      ‖∑ i ∈ range Hfine, (r (Hfine * b + i) : ℂ) *
        unitCharacter (((Hfine * b + i : ℕ) : ℝ) * β)‖ ≤ η * Hfine) (b : ℕ) :
    |∑ i ∈ range Hcoarse, g (Hcoarse * b + i) * r (Hcoarse * b + i)| ≤
      (ε + L * (η + 3 * (Hfine : ℝ) / Hcoarse)) * Hcoarse := by
  let : NeZero Hcoarse := ⟨hcoarse.ne'⟩
  let τ := η + 3 * (Hfine : ℝ) / Hcoarse
  have hcoarseR : (0 : ℝ) < Hcoarse := by exact_mod_cast hcoarse
  have hτ : τ * Hcoarse = η * Hcoarse + 3 * Hfine := by dsimp [τ]; field_simp
  have htest (j : Fin L) :
      ‖∑ i : Fin Hcoarse, (r (Hcoarse * b + i.val) : ℂ) *
        unitCharacter (((Hcoarse * b + i.val : ℕ) : ℝ) * α b j)‖ ≤ τ * Hcoarse := by
    have hn (n : ℕ) : ‖(r n : ℂ) * unitCharacter ((n : ℝ) * α b j)‖ ≤ 1 := by
      simpa only [norm_mul, unitCharacter_norm, mul_one, Complex.norm_real, Real.norm_eq_abs] using hr n
    have h := window_norm_bound_of_blocks
      (fun n => (r n : ℂ) * unitCharacter ((n : ℝ) * α b j)) hn
      Hfine (Hcoarse * b) Hcoarse hfine η hη0 hη1 (fun c => hfrequency c (α b j))
    rw [hτ]
    simpa only [Finset.sum_range] using h
  have h := finite_polynomial_correlation_bound
    (fun i : Fin Hcoarse => g (Hcoarse * b + i.val))
    (fun i : Fin Hcoarse => r (Hcoarse * b + i.val))
    (fun j (i : Fin Hcoarse) => unitCharacter (((Hcoarse * b + i.val : ℕ) : ℝ) * α b j))
    (a b) ε τ hε (fun i => hr _) (ha b)
    (by simpa only [Fintype.card_fin] using happrox b)
    (fun j => by simpa only [Fintype.card_fin] using htest j)
  simpa only [Finset.sum_range, Fintype.card_fin] using h

theorem cross_scale_prefix_correlation_bound
    (g r : ℕ → ℝ) (hg : ∀ n, g n ∈ Set.Icc (0 : ℝ) 1) (hr : ∀ n, |r n| ≤ 1)
    (Hfine Hcoarse L N : ℕ) (hfine : 0 < Hfine) (hcoarse : 0 < Hcoarse) (hN : 0 < N)
    (ε η : ℝ) (hε : 0 ≤ ε) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (a : ℕ → Fin L → ℂ) (α : ℕ → Fin L → ℝ)
    (ha : ∀ b j, ‖a b j‖ ≤ 1)
    (happrox : ∀ b,
      (∑ i : Fin Hcoarse, ‖(g (Hcoarse * b + i.val) : ℂ) -
        ∑ j, a b j * unitCharacter (((Hcoarse * b + i.val : ℕ) : ℝ) * α b j)‖ ^ 2) /
          Hcoarse ≤ ε ^ 2)
    (hfrequency : ∀ b β,
      ‖∑ i ∈ range Hfine, (r (Hfine * b + i) : ℂ) *
        unitCharacter (((Hfine * b + i : ℕ) : ℝ) * β)‖ ≤ η * Hfine) :
    |prefixCorrelation g r N| ≤ ε + L * (η + 3 * (Hfine : ℝ) / Hcoarse) + (Hcoarse : ℝ) / N := by
  let A := ε + L * (η + 3 * (Hfine : ℝ) / Hcoarse)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbound (n : ℕ) : ‖((g n * r n : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg n).1]
    exact (mul_le_mul (hg n).2 (hr n) (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hblock (b : ℕ) : ‖∑ i ∈ range Hcoarse, ((g (Hcoarse * b + i) * r (Hcoarse * b + i) : ℝ) : ℂ)‖ ≤ A * Hcoarse := by
    have h := coarse_block_correlation_bound g r hr Hfine Hcoarse L hfine hcoarse ε η hε hη0 hη1
      a α ha happrox hfrequency b
    simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using h
  have hprefix := prefix_norm_bound_of_block_norm_bound
    (fun n => ((g n * r n : ℝ) : ℂ)) hbound Hcoarse N hcoarse A hA hblock
  have hreal : |∑ n ∈ range N, g n * r n| ≤ A * N + Hcoarse := by
    simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using hprefix
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [prefixCorrelation, abs_div, abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  have heq : (A + (Hcoarse : ℝ) / N) * N = A * N + Hcoarse := by field_simp
  change |∑ n ∈ range N, g n * r n| ≤ (A + (Hcoarse : ℝ) / N) * N
  rw [heq]
  exact hreal

end Erdos335.IntermediateScale
