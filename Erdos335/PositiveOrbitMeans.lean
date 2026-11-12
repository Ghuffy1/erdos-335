import Erdos335.IntervalCharacterMeans
import Erdos335.PrincipalFrequencies

/-!
# Lower bounds for orbit means with nonnegative Fourier coefficients
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem intervalCharacterMean_sub_one_le (β : ℝ) (a L : ℕ) (hL : 0 < L) :
    ‖intervalCharacterMean β a L - 1‖ ≤
      ((a + L : ℕ) : ℝ) * ‖unitCharacter β - 1‖ := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have heq : intervalCharacterMean β a L - 1 =
      (∑ m ∈ range L, (unitCharacter (((a + m : ℕ) : ℝ) * β) - 1)) / (L : ℂ) := by
    simp only [intervalCharacterMean, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    field_simp
    simp only [mul_comm β]
  rw [heq, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hLR).mpr
  calc
    _ ≤ ∑ m ∈ range L, ‖unitCharacter (((a + m : ℕ) : ℝ) * β) - 1‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ range L, ((a + L : ℕ) : ℝ) * ‖unitCharacter β - 1‖ := by
      apply sum_le_sum
      intro m hm
      rw [unitCharacter_nat_mul]
      exact (unit_pow_sub_one_le _ (unitCharacter_norm β) (a + m)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.add_le_add_left (mem_range.mp hm).le a))
          (norm_nonneg _))
    _ = _ := by simp; ring

theorem unitCharacter_distance_bounds (β : ℝ) :
    4 * circleFrequencyDistance β ≤ ‖unitCharacter β - 1‖ ∧
      ‖unitCharacter β - 1‖ ≤ 2 * Real.pi * circleFrequencyDistance β := by
  rw [← unitCharacter_principalFrequency β]
  exact ⟨unitCharacter_sub_one_lower _ (circleFrequencyDistance_mem β).2,
    unitCharacter_sub_one_upper _⟩

theorem positive_weighted_real_sum_lower {I : Type*} [Fintype I]
    (c : I → ℝ) (z : I → ℂ) (i₀ : I) (E : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hE : 0 ≤ E) (hz0 : z i₀ = 1)
    (hz : ∀ i, i ≠ i₀ → -E ≤ (z i).re) :
    c i₀ - (∑ i, c i) * E ≤ (∑ i, (c i : ℂ) * z i).re := by
  classical
  have hi (i : I) : (if i = i₀ then c i₀ else 0) - c i * E ≤ c i * (z i).re := by
    by_cases heq : i = i₀
    · subst i
      simp only [hz0, Complex.one_re, mul_one, ite_true]
      exact sub_le_self _ (mul_nonneg (hc _) hE)
    · simp only [heq, ite_false, zero_sub]
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left (hz i heq) (hc i)
  have h := sum_le_sum fun i (_hi : i ∈ (univ : Finset I)) => hi i
  change c i₀ - (∑ i, c i) * E ≤ Complex.reCLM (∑ i, (c i : ℂ) * z i)
  rw [map_sum]
  simpa only [sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, ← sum_mul,
    Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

theorem intervalCharacterMean_real_lower (β : ℝ) (a L : ℕ) (hL : 0 < L)
    (δ κ : ℝ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hdichotomy : circleFrequencyDistance β ≤ δ ∨ κ ≤ ‖unitCharacter β - 1‖) :
    -((((a + L : ℕ) : ℝ) * (2 * Real.pi * δ)) + 2 / ((L : ℝ) * κ)) ≤
      (intervalCharacterMean β a L).re := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsmall : 0 ≤ ((a + L : ℕ) : ℝ) * (2 * Real.pi * δ) := by positivity
  have hlarge : 0 ≤ 2 / ((L : ℝ) * κ) := by positivity
  rcases hdichotomy with hs | hl
  · have he := intervalCharacterMean_sub_one_le β a L hL
    have he' : ‖intervalCharacterMean β a L - 1‖ ≤
        ((a + L : ℕ) : ℝ) * (2 * Real.pi * δ) := by
      apply he.trans
      gcongr
      exact (unitCharacter_distance_bounds β).2.trans (by gcongr)
    have hr := Complex.abs_re_le_norm (intervalCharacterMean β a L - 1)
    simp only [Complex.sub_re, Complex.one_re] at hr
    have hab := neg_le_abs ((intervalCharacterMean β a L).re - 1)
    linarith
  · have hn : unitCharacter β ≠ 1 := by
      intro he
      rw [he, sub_self, norm_zero] at hl
      linarith
    have he := intervalCharacterMean_norm_le β a L hn
    have he' : ‖intervalCharacterMean β a L‖ ≤ 2 / ((L : ℝ) * κ) := by
      apply he.trans
      exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hLR hκ)
        (mul_le_mul_of_nonneg_left hl hLR.le)
    have hr := Complex.abs_re_le_norm (intervalCharacterMean β a L)
    have hab := neg_le_abs (intervalCharacterMean β a L).re
    linarith

end Erdos335.IntermediateScale
