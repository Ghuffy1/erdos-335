import Erdos335.PolynomialWindowPeriods
import Erdos335.RoundedPeriodWindows

/-!
# Short divisible periods for a polynomial approximation
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_divisible_polynomial_window_periods {d : ℕ}
    (R : ℕ) (hR : 0 < R) (M : ℕ) (hM : 0 < M)
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ ∀ (c : ℕ → Fin d → ℂ) (α : ℕ → Fin d → ℝ)
      (w : ℕ → ℂ) (N W : ℕ) (C δ : ℝ),
      0 < N → 8 * (M : ℝ) / ε ≤ W → 0 ≤ δ →
      (∀ n i, ‖c n i‖ ≤ 1) →
      (∀ n, ‖w n - variableFrequencyPolynomial c α n‖ ≤ C) →
      (∑ n ∈ range N, ‖w n - variableFrequencyPolynomial c α n‖ ^ 2) / N ≤ δ ^ 2 →
      ∃ Q : ℕ → ℕ, (∀ n, M ∣ Q n ∧ W ≤ Q n ∧ (Q n : ℝ) < (1 + ε) * W) ∧
        averagedWindowTranslationError w Q N (R * W) ≤
          4 * δ + d * η + (2 * d : ℝ) *
            ((badFrequencyCombinationWindows N W K α ∪
              varyingPolynomialParameters N (3 * (R * W)) c α).card : ℝ) / N +
            10 * C * ((R * W : ℕ) : ℝ) / N := by
  classical
  obtain ⟨K, hK, hperiod⟩ := exists_short_divisible_phase_period_constant (I := Fin d)
    M hM η ε hη hε hε1
  refine ⟨K, hK, ?_⟩
  intro c α w N W C δ hN hlarge hδ hc he herror
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hWr : (0 : ℝ) < W := (div_pos (by positivity) hε).trans_le hlarge
  have hW : 0 < W := by exact_mod_cast hWr
  have hRW : 0 < R * W := Nat.mul_pos hR hW
  have hWleRW : W ≤ R * W := by nlinarith
  have htwice (q : ℕ) (hq : (q : ℝ) < (1 + ε) * W) : q ≤ 2 * W := by
    have hqr : (q : ℝ) ≤ 2 * W := by nlinarith
    exact_mod_cast hqr
  obtain ⟨a, L, ha, haW, hWa, hLa, hLlow, htop⟩ :=
    exists_short_divisible_window M W hM ε hε hε1 hlarge
  have hLr : (0 : ℝ) < L := (mul_pos (by positivity) (by exact_mod_cast ha)).trans_le hLlow
  have hL : 0 < L := by exact_mod_cast hLr
  have hdefault : ((M * a : ℕ) : ℝ) < (1 + ε) * W := by
    have hlt : M * a < M * (a + L) := Nat.mul_lt_mul_of_pos_left (by omega) hM
    exact (show ((M * a : ℕ) : ℝ) < ((M * (a + L) : ℕ) : ℝ) by exact_mod_cast hlt).trans_le htop
  let E := badFrequencyCombinationWindows N W K α ∪ varyingPolynomialParameters N (3 * (R * W)) c α
  let P := variableFrequencyPolynomial c α
  have hchoice (n : ℕ) : ∃ q : ℕ, M ∣ q ∧ W ≤ q ∧ (q : ℝ) < (1 + ε) * W ∧ q ≤ 2 * (R * W) ∧
      (n ∈ range N → n ∉ E → ∀ t < R * W, ‖P (n + t + q) - P (n + t)‖ ≤ d * η) := by
    by_cases hn : n < N ∧ n ∉ E
    · have hf : n ∉ badFrequencyCombinationWindows N W K α :=
        fun h => hn.2 (mem_union_left _ h)
      have hp : n ∉ varyingPolynomialParameters N (3 * (R * W)) c α :=
        fun h => hn.2 (mem_union_right _ h)
      obtain ⟨q, hMq, hWq, hqhi, hphase⟩ := hperiod (α n) W hlarge
        (frequency_gap_of_not_mem_bad_windows α N W K n hn.1 hf)
      have hqRW : q ≤ 2 * (R * W) := (htwice q hqhi).trans (by omega)
      refine ⟨q, hMq, hWq, hqhi, hqRW, ?_⟩
      intro hnN hgood t ht
      exact variable_polynomial_translation_of_not_mem c α N n t q (R * W) hn.1 ht.le
        hqRW η (hc n) (fun j => (hphase j).le) hp
    · exact ⟨M * a, dvd_mul_right _ _, hWa, hdefault, (htwice _ hdefault).trans (by omega),
        fun hnN hgood => (hn ⟨mem_range.mp hnN, hgood⟩).elim⟩
  choose Q hQ using hchoice
  refine ⟨Q, fun n => ⟨(hQ n).1, (hQ n).2.1, (hQ n).2.2.1⟩, ?_⟩
  apply window_translation_error_transfer w P Q N (R * W) hN hRW (fun n => (hQ n).2.2.2.1)
    C δ (d * η) (2 * d) hδ (by positivity) (by positivity) he herror E
  · intro n hn t ht
    exact (norm_sub_le _ _).trans (by
      have h1 := variableFrequencyPolynomial_norm_le c α hc (n + t + Q n)
      have h0 := variableFrequencyPolynomial_norm_le c α hc (n + t)
      dsimp [P]
      linarith)
  · intro n hn hgood t ht
    exact (hQ n).2.2.2.2 hn hgood t ht

end Erdos335.IntermediateScale
