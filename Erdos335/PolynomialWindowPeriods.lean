import Erdos335.GoodFrequencyWindowPeriods
import Erdos335.WindowTranslationTransfer

/-!
# Averaged approximate periods of an ordinary polynomial model
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem variableFrequencyPolynomial_norm_le {d : ℕ}
    (c : ℕ → Fin d → ℂ) (α : ℕ → Fin d → ℝ)
    (hc : ∀ n i, ‖c n i‖ ≤ 1) (n : ℕ) :
    ‖variableFrequencyPolynomial c α n‖ ≤ d := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin d, (1 : ℝ) := by
      apply sum_le_sum
      intro i hi
      simpa only [norm_mul, unitCharacter_norm, mul_one] using hc n i
    _ = _ := by simp

theorem exists_polynomial_window_periods {d : ℕ} (η ρ : ℝ)
    (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ K : ℕ, 0 < K ∧ ∀ (c : ℕ → Fin d → ℂ) (α : ℕ → Fin d → ℝ)
      (w : ℕ → ℂ) (N W L : ℕ) (C δ : ℝ),
      0 < N → 0 < W → L ≤ W → ρ * W ≤ L → 0 ≤ δ →
      (∀ n i, ‖c n i‖ ≤ 1) →
      (∀ n, ‖w n - variableFrequencyPolynomial c α n‖ ≤ C) →
      (∑ n ∈ range N, ‖w n - variableFrequencyPolynomial c α n‖ ^ 2) / N ≤ δ ^ 2 →
      ∃ Q : ℕ → ℕ, (∀ n, W ≤ Q n ∧ Q n ≤ 2 * W) ∧
        averagedWindowTranslationError w Q N W ≤
          4 * δ + d * η + (2 * d : ℝ) *
            ((badFrequencyCombinationWindows N W K α ∪
              varyingPolynomialParameters N (3 * W) c α).card : ℝ) / N +
            10 * C * (W : ℝ) / N := by
  classical
  obtain ⟨K, hK, hperiod⟩ := exists_polynomial_period_constant (d := d) η ρ hη hρ
  refine ⟨K, hK, ?_⟩
  intro c α w N W L C δ hN hW hLW hρW hδ hc he herror
  let E := badFrequencyCombinationWindows N W K α ∪ varyingPolynomialParameters N (3 * W) c α
  let P := variableFrequencyPolynomial c α
  have hchoice (n : ℕ) : ∃ q : ℕ, W ≤ q ∧ q ≤ 2 * W ∧
      (n ∈ range N → n ∉ E → ∀ t < W, ‖P (n + t + q) - P (n + t)‖ ≤ d * η) := by
    by_cases hn : n < N ∧ n ∉ E
    · have hf : n ∉ badFrequencyCombinationWindows N W K α :=
        fun h => hn.2 (mem_union_left _ h)
      have hp : n ∉ varyingPolynomialParameters N (3 * W) c α :=
        fun h => hn.2 (mem_union_right _ h)
      obtain ⟨q, hqlo, hqhi, hq⟩ := hperiod c α N n W L hn.1 hW hLW hρW (hc n) hf hp
      exact ⟨q, hqlo, by omega, fun _ _ t ht => hq t ht.le⟩
    · exact ⟨W, le_rfl, by omega, fun hnN hgood => (hn ⟨mem_range.mp hnN, hgood⟩).elim⟩
  choose Q hQ using hchoice
  refine ⟨Q, fun n => ⟨(hQ n).1, (hQ n).2.1⟩, ?_⟩
  apply window_translation_error_transfer w P Q N W hN hW (fun n => (hQ n).2.1)
    C δ (d * η) (2 * d) hδ (by positivity) (by positivity) he herror E
  · intro n hn t ht
    exact (norm_sub_le _ _).trans (by
      have h1 := variableFrequencyPolynomial_norm_le c α hc (n + t + Q n)
      have h0 := variableFrequencyPolynomial_norm_le c α hc (n + t)
      dsimp [P]
      linarith)
  · intro n hn hgood t ht
    exact (hQ n).2.2 hn hgood t ht

end Erdos335.IntermediateScale
