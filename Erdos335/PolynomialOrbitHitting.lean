import Erdos335.IntervalCharacterMeans

/-!
# A finite Fourier criterion for a large value on an integer orbit segment
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem orbit_polynomial_mean_bound {I : Type*} [Fintype I]
    (c : I → ℂ) (β : I → ℝ) (i₀ : I) (a L : ℕ) (hL : 0 < L)
    (κ : ℝ) (hκ : 0 < κ) (hzero : β i₀ = 0)
    (hfreq : ∀ i, i ≠ i₀ → κ ≤ ‖unitCharacter (β i) - 1‖) :
    ‖((∑ m ∈ range L, ∑ i, c i * unitCharacter (((a + m : ℕ) : ℝ) * β i)) / (L : ℂ)) - c i₀‖ ≤
      (∑ i, ‖c i‖) * (2 / ((L : ℝ) * κ)) := by
  classical
  let η := 2 / ((L : ℝ) * κ)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hmean : ((∑ m ∈ range L, ∑ i, c i * unitCharacter (((a + m : ℕ) : ℝ) * β i)) / (L : ℂ)) =
      ∑ i, c i * intervalCharacterMean (β i) a L := by
    rw [sum_comm, sum_div]
    apply sum_congr rfl
    intro i hi
    dsimp only [intervalCharacterMean]
    rw [← mul_sum, mul_div_assoc]
  have hm0 : intervalCharacterMean (β i₀) a L = 1 := by
    simp [hzero, intervalCharacterMean, unitCharacter, hL.ne']
  have hm (i : I) (hi : i ≠ i₀) : ‖intervalCharacterMean (β i) a L‖ ≤ η := by
    have hd : 0 < ‖unitCharacter (β i) - 1‖ := hκ.trans_le (hfreq i hi)
    have hne : unitCharacter (β i) ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp hd)
    calc
      _ ≤ 2 / ((L : ℝ) * ‖unitCharacter (β i) - 1‖) := intervalCharacterMean_norm_le (β i) a L hne
      _ ≤ η := div_le_div_of_nonneg_left (by norm_num) (mul_pos hLr hκ)
        (mul_le_mul_of_nonneg_left (hfreq i hi) hLr.le)
  have heq : (∑ i, c i * intervalCharacterMean (β i) a L) - c i₀ =
      ∑ i, c i * (intervalCharacterMean (β i) a L - if i = i₀ then 1 else 0) := by
    simp only [mul_sub, sum_sub_distrib]
    simp
  rw [hmean, heq]
  calc
    _ ≤ ∑ i, ‖c i * (intervalCharacterMean (β i) a L - if i = i₀ then 1 else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ * η := by
      apply sum_le_sum
      intro i hi
      by_cases he : i = i₀
      · subst i
        simp only [hm0, ite_true, sub_self, mul_zero, norm_zero]
        exact mul_nonneg (norm_nonneg _) hη
      · simp only [he, ite_false, sub_zero, norm_mul]
        exact mul_le_mul_of_nonneg_left (hm i he) (norm_nonneg _)
    _ = _ := by rw [sum_mul]

theorem exists_large_orbit_polynomial_value {I : Type*} [Fintype I]
    (c : I → ℂ) (β : I → ℝ) (i₀ : I) (a L : ℕ) (hL : 0 < L)
    (κ δ : ℝ) (hκ : 0 < κ) (hzero : β i₀ = 0)
    (hfreq : ∀ i, i ≠ i₀ → κ ≤ ‖unitCharacter (β i) - 1‖)
    (hmass : δ + (∑ i, ‖c i‖) * (2 / ((L : ℝ) * κ)) < ‖c i₀‖) :
    ∃ m < L, δ < ‖∑ i, c i * unitCharacter (((a + m : ℕ) : ℝ) * β i)‖ := by
  classical
  by_contra! h
  let P := fun m => ∑ i, c i * unitCharacter (((a + m : ℕ) : ℝ) * β i)
  let z := (∑ m ∈ range L, P m) / (L : ℂ)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hz : ‖z‖ ≤ δ := by
    rw [show z = (∑ m ∈ range L, P m) / (L : ℂ) from rfl, norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hLr).mpr
    calc
      _ ≤ ∑ m ∈ range L, ‖P m‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ range L, δ := sum_le_sum fun m hm => h m (mem_range.mp hm)
      _ = δ * L := by simp; ring
  have he := orbit_polynomial_mean_bound c β i₀ a L hL κ hκ hzero hfreq
  have ht := norm_sub_le z (z - c i₀)
  have heq : z - (z - c i₀) = c i₀ := by ring
  rw [heq] at ht
  change ‖z - c i₀‖ ≤ _ at he
  linarith

end Erdos335.IntermediateScale
