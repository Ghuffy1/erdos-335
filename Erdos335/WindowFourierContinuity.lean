import Erdos335.WindowShiftAverages
import Erdos335.FinitePolynomialCorrelation
import Erdos335.PrefixEnergyAlgebra

/-!
# Mean-square continuity of averaged moving-window Fourier norms
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem windowFourierNorm_difference_bound (r r' : ℕ → ℝ) (n W : ℕ) :
    windowFourierNorm r n W ≤ windowFourierNorm r' n W +
      (∑ i ∈ range W, |r (n + i) - r' (n + i)|) / W := by
  apply windowFourierNorm_le_of_coefficients
  intro β
  let a := (∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)) / (W : ℂ)
  let b := (∑ i ∈ range W, (r' (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)) / (W : ℂ)
  have heq : a - b = (∑ i ∈ range W,
      ((r (n + i) - r' (n + i) : ℝ) : ℂ) * unitCharacter ((i : ℝ) * β)) / (W : ℂ) := by
    simp only [a, b, Complex.ofReal_sub, sub_mul, sum_sub_distrib, sub_div]
  have hd := window_fourier_coefficient_le_abs_average (fun k => r k - r' k) n W β
  rw [← heq] at hd
  have hb : ‖b‖ ≤ windowFourierNorm r' n W :=
    le_ciSup (window_fourier_coefficients_bddAbove r' n W) β
  have ht := norm_add_le (a - b) b
  rw [sub_add_cancel] at ht
  exact ht.trans (add_le_add hd hb |>.trans_eq (add_comm _ _))

theorem averaged_windowFourierNorm_difference_bound (r r' : ℕ → ℝ)
    (hr : ∀ n, |r n| ≤ 1) (hr' : ∀ n, |r' n| ≤ 1)
    (N W : ℕ) (hN : 0 < N) (hW : 0 < W) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : prefixEnergy (fun n => r n - r' n) N ≤ δ ^ 2) :
    (∑ n ∈ range N, windowFourierNorm r n W) / N ≤
      (∑ n ∈ range N, windowFourierNorm r' n W) / N + δ + 2 * (W : ℝ) / N := by
  let e := fun n => |r n - r' n|
  have heBound (n : ℕ) : e n ∈ Set.Icc (0 : ℝ) 2 := by
    refine ⟨abs_nonneg _, ?_⟩
    have h := norm_sub_le (r n) (r' n)
    simp only [Real.norm_eq_abs] at h
    exact h.trans (by linarith [hr n, hr' n])
  let : NeZero N := ⟨hN.ne'⟩
  have hL1 : (∑ n ∈ range N, e n) ≤ δ * N := by
    have h := finite_l1_of_mean_square (fun n : Fin N => ((r n.val - r' n.val : ℝ) : ℂ)) δ hδ
      (by simpa only [Fintype.card_fin, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Finset.sum_range, prefixEnergy] using he)
    simpa only [e, Fintype.card_fin, Complex.norm_real, Real.norm_eq_abs, Finset.sum_range] using h
  have hpoint := sum_le_sum fun n (_hn : n ∈ range N) => windowFourierNorm_difference_bound r r' n W
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := div_le_div_of_nonneg_right hpoint hNr.le
  rw [sum_add_distrib, add_div] at hsum
  have havg := averaged_window_sum_le e 2 heBound N W hN hW
  have hL1div : (∑ n ∈ range N, e n) / N ≤ δ := by
    exact (div_le_iff₀ hNr).mpr hL1
  change (∑ n ∈ range N, windowFourierNorm r n W) / N ≤ _ at hsum
  change (∑ n ∈ range N, (∑ i ∈ range W, e (n + i)) / W) / N ≤ _ at havg
  dsimp [e] at havg hL1div
  linarith

end Erdos335.IntermediateScale
