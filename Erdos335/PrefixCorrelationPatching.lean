import Erdos335.CrossScaleBlockCorrelation
import Erdos335.PrefixBlockStitching

/-!
# Correlation errors confined to an initial segment
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_supported_abs_sum_bound (v : ℕ → ℝ) (N L : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ n, |v n| ≤ C) (hsupport : ∀ n, L ≤ n → n < N → v n = 0) :
    |∑ n ∈ range N, v n| ≤ C * L := by
  classical
  have hcard : ((range N).filter (fun n => n < L)).card ≤ L := by
    calc
      _ ≤ (range L).card := card_le_card (fun n hn => mem_range.mpr (mem_filter.mp hn).2)
      _ = L := card_range L
  calc
    _ = ‖∑ n ∈ range N, v n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑ n ∈ range N, ‖v n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range N, if n < L then C else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases h : n < L
      · simpa only [h, ite_true, Real.norm_eq_abs] using hv n
      · simp only [h, ite_false, hsupport n (by omega) (mem_range.mp hn), norm_zero]
        exact le_rfl
    _ = (((range N).filter (fun n => n < L)).card : ℝ) * C := by
      simp only [sum_ite, sum_const, nsmul_eq_mul, mul_zero, add_zero]
    _ ≤ C * L := by
      have hc : (((range N).filter (fun n => n < L)).card : ℝ) ≤ L := by exact_mod_cast hcard
      nlinarith

theorem prefix_patch_correlation_bound (F g h g' h' : ℕ → ℝ) (N L : ℕ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ n, g n ∈ Set.Icc (0 : ℝ) 1) (hh : ∀ n, h n ∈ Set.Icc (0 : ℝ) 1)
    (hg' : ∀ n, g' n ∈ Set.Icc (0 : ℝ) 1) (hh' : ∀ n, h' n ∈ Set.Icc (0 : ℝ) 1)
    (heq : ∀ n, L ≤ n → n < N → g n = g' n ∧ h n = h' n) :
    |prefixCorrelation g (fun n => F n - h n) N -
      prefixCorrelation g' (fun n => F n - h' n) N| ≤ 2 * (L : ℝ) / N := by
  let v := fun n => g n * (F n - h n) - g' n * (F n - h' n)
  have hproduct (u w : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1)
      (hw : ∀ n, w n ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) : |u n * (F n - w n)| ≤ 1 := by
    have hdiff : |F n - w n| ≤ 1 := abs_le.mpr
      ⟨by linarith [(hF n).1, (hw n).2], by linarith [(hF n).2, (hw n).1]⟩
    rw [abs_mul, abs_of_nonneg (hu n).1]
    exact (mul_le_mul (hu n).2 hdiff (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hv (n : ℕ) : |v n| ≤ 2 := by
    have hn := norm_sub_le (g n * (F n - h n)) (g' n * (F n - h' n))
    simp only [Real.norm_eq_abs] at hn
    dsimp [v]
    linarith [hproduct g h hg hh n, hproduct g' h' hg' hh' n]
  have hz (n : ℕ) (hL : L ≤ n) (hN : n < N) : v n = 0 := by
    obtain ⟨h1, h2⟩ := heq n hL hN
    simp only [v, h1, h2, sub_self]
  have hsum := prefix_supported_abs_sum_bound v N L 2 (by norm_num) hv hz
  have hequiv : prefixCorrelation g (fun n => F n - h n) N -
      prefixCorrelation g' (fun n => F n - h' n) N = (∑ n ∈ range N, v n) / N := by
    simp only [prefixCorrelation, sub_div, sum_sub_distrib, v]
  rw [hequiv, abs_div, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)

end Erdos335.IntermediateScale
