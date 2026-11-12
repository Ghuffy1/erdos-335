import Erdos335.IntermediateFourierModel
import Erdos335.IntermediateConvolutionPeriods

/-!
# Period and residual data at a chosen common scale
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_fourier_model_period_data {F : ℕ → ℝ} {N A B : ℕ → ℕ}
    (m : IntermediateFourierModel F N A B) (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hN : ∀ s, 0 < N s) (H : ℕ → ℕ) (hHpos : ∀ s, 0 < H s)
    (hH : Tendsto H atTop atTop)
    (hAH : Tendsto (fun s => (A s : ℝ) / H s) atTop (𝓝 0))
    (hHB : Tendsto (fun s => (H s : ℝ) / B s) atTop (𝓝 0))
    (hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0)) :
    ∃ (Q : ℕ → ℕ → ℕ) (ε : ℕ → ℝ),
      (∀ s, 0 < ε s) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ᶠ s in atTop, ∀ n, H s ≤ Q s n ∧ (Q s n : ℝ) ≤ (1 + ε s) * H s) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, ∀ n, M ∣ Q s n) ∧
      Tendsto (fun s => averagedWindowTranslationError (fun n => (m.structured n : ℂ))
        (Q s) (N s) (6 * H s)) atTop (𝓝 0) ∧
      Tendsto (fun s => (∑ n ∈ Finset.range (N s),
        windowFourierNorm (fun n => F n - m.structured n) n (6 * H s)) / N s) atTop (𝓝 0) := by
  obtain ⟨Q, ε, hεpos, hεlim, hQ, hdiv, hperiod⟩ :=
    (intermediate_fourier_convolution_and_periods 6 (by decide) F m.structured hF m.bounded
      m.dimension m.coefficient m.frequency m.coefficient_bound N A B hN m.approximation
      (fun W hW hAW hWB => m.control W (Eventually.of_forall hW) hAW hWB)
      H hHpos hH hAH hHB hHN).2
  have hA6H : Tendsto (fun s => (A s : ℝ) / (6 * H s : ℕ)) atTop (𝓝 0) := by
    have heq : (fun s => (A s : ℝ) / (6 * H s : ℕ)) = fun s => ((A s : ℝ) / H s) / 6 := by
      funext s
      push_cast
      ring
    rw [heq]
    simpa only [zero_div] using hAH.div_const 6
  have h6HB : Tendsto (fun s => ((6 * H s : ℕ) : ℝ) / B s) atTop (𝓝 0) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, mul_zero] using hHB.const_mul 6
  exact ⟨Q, ε, hεpos, hεlim, hQ, hdiv, hperiod,
    (m.control (fun s => 6 * H s)
      (Eventually.of_forall fun s => Nat.mul_pos (by decide) (hHpos s)) hA6H h6HB).1⟩

end Erdos335.IntermediateScale
