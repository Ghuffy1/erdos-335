import Erdos335.WindowShiftAverages
import Erdos335.FinitePolynomialCorrelation

/-!
# Averaging nonnegative errors after a position-dependent short shift
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem shifted_window_sum_le_extended_window (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (n Q W : ℕ) (hQ : Q ≤ 2 * W) :
    (∑ h ∈ range W, f (n + h + Q)) ≤ ∑ h ∈ range (3 * W), f (n + h) := by
  have hsplit := sum_range_add (fun h => f (n + h)) Q W
  have hnonneg : 0 ≤ ∑ h ∈ range Q, f (n + h) := sum_nonneg fun h hh => hf _
  have hfirst : (∑ h ∈ range W, f (n + (Q + h))) ≤ ∑ h ∈ range (Q + W), f (n + h) := by
    linarith
  have hsecond : (∑ h ∈ range (Q + W), f (n + h)) ≤ ∑ h ∈ range (3 * W), f (n + h) := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    intro h hh hnot
    exact hf _
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst.trans hsecond

theorem variable_shifted_window_average_le (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) C) (Q : ℕ → ℕ)
    (N W : ℕ) (hN : 0 < N) (hW : 0 < W) (hQ : ∀ n, Q n ≤ 2 * W) :
    (∑ n ∈ range N, (∑ h ∈ range W, f (n + h + Q n)) / W) / N ≤
      3 * ((∑ n ∈ range N, f n) / N) + 9 * C * (W : ℝ) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hfirst :
      (∑ n ∈ range N, (∑ h ∈ range W, f (n + h + Q n)) / W) / N ≤
        (∑ n ∈ range N, (∑ h ∈ range (3 * W), f (n + h)) / W) / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    apply sum_le_sum
    intro n hn
    exact div_le_div_of_nonneg_right
      (shifted_window_sum_le_extended_window f (fun n => (hf n).1) n (Q n) W (hQ n)) hWr.le
  have hbig := averaged_window_sum_le f C hf N (3 * W) hN (by omega)
  have heq : (∑ n ∈ range N, (∑ h ∈ range (3 * W), f (n + h)) / W) / N =
      3 * ((∑ n ∈ range N, (∑ h ∈ range (3 * W), f (n + h)) / (3 * W : ℕ)) / N) := by
    rw [← sum_div, ← sum_div]
    push_cast
    field_simp
  rw [heq] at hfirst
  have hscaled := mul_le_mul_of_nonneg_left hbig (by norm_num : (0 : ℝ) ≤ 3)
  push_cast at hfirst
  push_cast at hscaled
  calc
    _ ≤ 3 * ((∑ n ∈ range N, f n) / N + C * (3 * (W : ℝ)) / N) := hfirst.trans hscaled
    _ = _ := by ring

theorem variable_shifted_error_average_le (e : ℕ → ℂ) (C δ : ℝ)
    (he : ∀ n, ‖e n‖ ≤ C) (hδ : 0 ≤ δ) (Q : ℕ → ℕ)
    (N W : ℕ) (hN : 0 < N) (hW : 0 < W) (hQ : ∀ n, Q n ≤ 2 * W)
    (herror : (∑ n ∈ range N, ‖e n‖ ^ 2) / N ≤ δ ^ 2) :
    (∑ n ∈ range N, (∑ h ∈ range W, ‖e (n + h + Q n)‖) / W) / N ≤
      3 * δ + 9 * C * (W : ℝ) / N := by
  let : NeZero N := ⟨hN.ne'⟩
  have hL1 : (∑ n ∈ range N, ‖e n‖) ≤ δ * N := by
    have h := finite_l1_of_mean_square (fun n : Fin N => e n.val) δ hδ
      (by simpa only [Fintype.card_fin, Finset.sum_range] using herror)
    simpa only [Fintype.card_fin, Finset.sum_range] using h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hL1div : (∑ n ∈ range N, ‖e n‖) / N ≤ δ := (div_le_iff₀ hNr).mpr hL1
  have hb := variable_shifted_window_average_le (fun n => ‖e n‖) C
    (fun n => ⟨norm_nonneg _, he n⟩) Q N W hN hW hQ
  calc
    _ ≤ 3 * ((∑ n ∈ range N, ‖e n‖) / N) + 9 * C * (W : ℝ) / N := hb
    _ ≤ _ := by gcongr

end Erdos335.IntermediateScale
