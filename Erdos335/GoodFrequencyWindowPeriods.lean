import Erdos335.SimultaneousApproximatePeriod
import Erdos335.VariablePolynomialTranslation
import Erdos335.FrequencyCombinationWindows

/-!
# Approximate polynomial periods outside the exceptional frequency windows
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem frequency_gap_of_not_mem_bad_windows {d : ℕ}
    (α : ℕ → Fin d → ℝ) (N W C n : ℕ) (hn : n < N)
    (hgood : n ∉ badFrequencyCombinationWindows N W C α)
    (w : Fin d → ℤ) (hw : ∀ i, |w i| ≤ (C : ℤ)) :
    circleFrequencyDistance (∑ i, (w i : ℝ) * α n i) ≤ 1 / ((C : ℝ) * W) ∨
      (C : ℝ) / W ≤ circleFrequencyDistance (∑ i, (w i : ℝ) * α n i) := by
  classical
  by_contra! h
  obtain ⟨v, hv⟩ := boundedFrequencyWeights_represent w hw
  apply hgood
  apply mem_filter.mpr
  refine ⟨mem_range.mpr hn, v, ?_⟩
  simpa only [frequencyCombination, hv] using h

theorem exists_polynomial_period_constant {d : ℕ} (η ρ : ℝ)
    (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (c : ℕ → Fin d → ℂ) (α : ℕ → Fin d → ℝ)
      (N n W L : ℕ), n < N → 0 < W → L ≤ W → ρ * W ≤ L →
      (∀ i, ‖c n i‖ ≤ 1) → n ∉ badFrequencyCombinationWindows N W C α →
      n ∉ varyingPolynomialParameters N (3 * W) c α →
      ∃ Q : ℕ, W ≤ Q ∧ Q < W + L ∧ ∀ t ≤ W,
        ‖variableFrequencyPolynomial c α (n + t + Q) -
          variableFrequencyPolynomial c α (n + t)‖ ≤ d * η := by
  obtain ⟨C, hC, hperiod⟩ := exists_simultaneous_approximate_period_constant (I := Fin d) η ρ hη hρ
  refine ⟨C, hC, ?_⟩
  intro c α N n W L hn hW hLW hρW hc hfrequency hparameters
  obtain ⟨m, hm, hphase⟩ := hperiod (α n) W L W hW (by omega) hρW
    (frequency_gap_of_not_mem_bad_windows α N W C n hn hfrequency)
  refine ⟨W + m, by omega, by omega, ?_⟩
  intro t ht
  exact variable_polynomial_translation_of_not_mem c α N n t (W + m) W hn ht
    (by omega) η hc (fun j => (hphase j).le) hparameters

end Erdos335.IntermediateScale
