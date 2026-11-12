import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Field.GeomSum

/-!
# Character averages at separated lengths

These estimates supply the frequency-separation step in the intermediate-scale
argument of Ackelsberg--Richter, Theorem 8.7. The lower estimate uses the distance
of the short average from one directly.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

noncomputable def characterMean (z : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ j ∈ range n, z ^ (j + 1)

theorem unit_pow_sub_one_le (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ (n : ℝ) * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1) := by ring
    rw [heq]
    calc
      ‖z * (z ^ n - 1) + (z - 1)‖ ≤ ‖z * (z ^ n - 1)‖ + ‖z - 1‖ :=
        norm_add_le _ _
      _ = ‖z ^ n - 1‖ + ‖z - 1‖ := by rw [norm_mul, hz, one_mul]
      _ ≤ (n : ℝ) * ‖z - 1‖ + ‖z - 1‖ := add_le_add ih le_rfl
      _ = ((n + 1 : ℕ) : ℝ) * ‖z - 1‖ := by push_cast; ring

theorem characterMean_sub_one_le (z : ℂ) (hz : ‖z‖ = 1)
    (n : ℕ) (hn : 0 < n) :
    ‖characterMean z n - 1‖ ≤ (n : ℝ) * ‖z - 1‖ := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have heq : characterMean z n - 1 =
      (n : ℂ)⁻¹ * ∑ j ∈ range n, (z ^ (j + 1) - 1) := by
    simp only [characterMean, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      mul_one, mul_sub, inv_mul_cancel₀ hnC]
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (n : ℝ)⁻¹ * ‖∑ j ∈ range n, (z ^ (j + 1) - 1)‖ ≤
        (n : ℝ)⁻¹ * ∑ j ∈ range n, ‖z ^ (j + 1) - 1‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hnR.le)
    _ ≤ (n : ℝ)⁻¹ * ∑ _j ∈ range n, (n : ℝ) * ‖z - 1‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hnR.le)
      apply sum_le_sum
      intro j hj
      exact (unit_pow_sub_one_le z hz (j + 1)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_range.mp hj)) (norm_nonneg _))
    _ = (n : ℝ) * ‖z - 1‖ := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      field_simp

theorem characterMean_norm_le (z : ℂ) (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    ‖characterMean z n‖ ≤ 2 / ((n : ℝ) * ‖z - 1‖) := by
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have heq : (∑ j ∈ range n, z ^ (j + 1)) = z * ((z ^ n - 1) / (z - 1)) := by
    simp only [pow_succ, mul_comm (z ^ _) z, ← mul_sum]
    rw [geom_sum_eq hne]
  have hnum : ‖z ^ n - 1‖ ≤ 2 := by
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  rw [characterMean, heq, norm_mul, norm_inv, Complex.norm_natCast,
    norm_mul, hz, one_mul, norm_div]
  calc
    (n : ℝ)⁻¹ * (‖z ^ n - 1‖ / ‖z - 1‖) ≤
        (n : ℝ)⁻¹ * (2 / ‖z - 1‖) := by gcongr
    _ = 2 / ((n : ℝ) * ‖z - 1‖) := by ring

theorem characterMean_separation (z : ℂ) (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (short long : ℕ) (hs : 0 < short) (hl : 0 < long)
    (hshort : (short : ℝ) * ‖z - 1‖ ≤ 1 / 4)
    (hlong : 8 ≤ (long : ℝ) * ‖z - 1‖) :
    1 / 2 ≤ ‖characterMean z long - characterMean z short‖ := by
  have hsbound := characterMean_sub_one_le z hz short hs
  have hlbound := characterMean_norm_le z hz hne long hl
  have hlarge : ‖characterMean z long‖ ≤ 1 / 4 := by
    apply hlbound.trans
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) hlong)).mpr
    linarith
  have htriangle : ‖(1 : ℂ)‖ ≤ ‖characterMean z short - 1‖ +
      ‖characterMean z long - characterMean z short‖ + ‖characterMean z long‖ := by
    calc
      ‖(1 : ℂ)‖ = ‖(-1 : ℂ)‖ := (norm_neg _).symm
      _ = ‖(characterMean z short - 1) +
          (characterMean z long - characterMean z short) - characterMean z long‖ := by
        congr 1
        ring
      _ ≤ ‖(characterMean z short - 1) +
          (characterMean z long - characterMean z short)‖ + ‖characterMean z long‖ :=
        norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
  rw [norm_one] at htriangle
  linarith

end Erdos335.IntermediateScale
