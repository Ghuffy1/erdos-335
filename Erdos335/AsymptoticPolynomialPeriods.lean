import Erdos335.DivisiblePolynomialPeriods
import Erdos335.SlowDiagonalSelection

/-!
# Eventual divisible periods of an ordinary structured function
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem eventually_exists_structured_periods
    (R : ℕ) (hR : 0 < R) (w : ℕ → ℝ) (hw : ∀ n, w n ∈ Set.Icc (0 : ℝ) 1)
    (d : ℕ → ℕ) (c : ∀ k, ℕ → Fin (d k) → ℂ) (α : ∀ k, ℕ → Fin (d k) → ℝ)
    (hc : ∀ k n i, ‖c k n i‖ ≤ 1)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hH : Tendsto H atTop atTop)
    (hscale : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (happrox : ∀ δ > 0, ∃ k : ℕ, ∀ᶠ s in atTop,
      (∑ n ∈ range (N s), ‖(w n : ℂ) - variableFrequencyPolynomial (c k) (α k) n‖ ^ 2) /
        N s ≤ δ ^ 2)
    (hparameters : ∀ k, Tendsto (fun s =>
      ((varyingPolynomialParameters (N s) (3 * (R * H s)) (c k) (α k)).card : ℝ) / N s) atTop (𝓝 0))
    (hfrequency : ∀ k K : ℕ, 0 < K → Tendsto (fun s =>
      ((badFrequencyCombinationWindows (N s) (H s) K (α k)).card : ℝ) / N s) atTop (𝓝 0))
    (M : ℕ) (hM : 0 < M) (ε τ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ s in atTop, ∃ Q : ℕ → ℕ,
      (∀ n, M ∣ Q n ∧ H s ≤ Q n ∧ (Q n : ℝ) < (1 + ε) * H s) ∧
      averagedWindowTranslationError (fun n => (w n : ℂ)) Q (N s) (R * H s) < τ := by
  classical
  let δ := τ / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨k, hk⟩ := happrox δ hδ
  let η := τ / (8 * ((d k : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK, hperiod⟩ := exists_divisible_polynomial_window_periods (d := d k)
    R hR M hM η ε hη hε hε1
  let E := fun s => badFrequencyCombinationWindows (N s) (H s) K (α k) ∪
    varyingPolynomialParameters (N s) (3 * (R * H s)) (c k) (α k)
  have hE : Tendsto (fun s => ((E s).card : ℝ) / N s) atTop (𝓝 0) := by
    have hlim : Tendsto (fun s =>
        ((badFrequencyCombinationWindows (N s) (H s) K (α k)).card : ℝ) / N s +
        ((varyingPolynomialParameters (N s) (3 * (R * H s)) (c k) (α k)).card : ℝ) / N s)
        atTop (𝓝 0) := by simpa only [add_zero] using (hfrequency k K hK).add (hparameters k)
    apply squeeze_zero (fun s => by positivity) (fun s => ?_) hlim
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_union_le
      (badFrequencyCombinationWindows (N s) (H s) K (α k))
      (varyingPolynomialParameters (N s) (3 * (R * H s)) (c k) (α k))
  have he (n : ℕ) : ‖(w n : ℂ) - variableFrequencyPolynomial (c k) (α k) n‖ ≤
      (d k : ℝ) + 1 := by
    have hn : ‖(w n : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n).1] using (hw n).2
    have hp := variableFrequencyPolynomial_norm_le (c k) (α k) (hc k) n
    exact (norm_sub_le _ _).trans (by linarith)
  have hRscale : Tendsto (fun s => ((R * H s : ℕ) : ℝ) / N s) atTop (𝓝 0) := by
    simpa only [Nat.cast_mul, mul_div_assoc, mul_zero] using hscale.const_mul (R : ℝ)
  have htail : Tendsto (fun s => (2 * (d k : ℝ)) * (((E s).card : ℝ) / N s) +
      (10 * ((d k : ℝ) + 1)) * (((R * H s : ℕ) : ℝ) / N s)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hE.const_mul (2 * (d k : ℝ))).add
      (hRscale.const_mul (10 * ((d k : ℝ) + 1)))
  have hsmall := htail.eventually (gt_mem_nhds (show (0 : ℝ) < τ / 2 by positivity))
  have hlarge : ∀ᶠ s in atTop, 8 * (M : ℝ) / ε ≤ H s :=
    (tendsto_natCast_atTop_atTop.comp hH).eventually (eventually_ge_atTop _)
  have hfixed : 4 * δ + (d k : ℝ) * η < τ / 2 := by
    have heq : (8 * ((d k : ℝ) + 1)) * η = τ := by dsimp [η]; field_simp
    dsimp only [δ]
    nlinarith
  filter_upwards [hk, hsmall, hlarge] with s hs htailSmall hlargeS
  obtain ⟨Q, hQ, hbound⟩ := hperiod (c k) (α k) (fun n => (w n : ℂ))
    (N s) (H s) ((d k : ℝ) + 1) δ (hN s) hlargeS hδ.le (hc k) he hs
  refine ⟨Q, hQ, ?_⟩
  have htailSmall' : (2 * (d k : ℝ)) * ((E s).card : ℝ) / N s +
      10 * ((d k : ℝ) + 1) * ((R * H s : ℕ) : ℝ) / N s < τ / 2 := by
    simpa only [mul_div_assoc] using htailSmall
  change averagedWindowTranslationError _ _ _ _ ≤
    4 * δ + (d k : ℝ) * η + (2 * (d k : ℝ)) * ((E s).card : ℝ) / N s +
      10 * ((d k : ℝ) + 1) * ((R * H s : ℕ) : ℝ) / N s at hbound
  linarith

end Erdos335.IntermediateScale
