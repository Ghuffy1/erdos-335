import Erdos335.IntermediateFourierDecomposition
import Erdos335.IntermediateControlSubsequence

/-!
# Reusable data for intermediate Fourier models
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace Erdos335.IntermediateScale

structure IntermediateFourierModel (F : ℕ → ℝ) (N A B : ℕ → ℕ) where
  structured : ℕ → ℝ
  dimension : ℕ → ℕ
  coefficient : ∀ k, ℕ → Fin (dimension k) → ℂ
  frequency : ∀ k, ℕ → Fin (dimension k) → ℝ
  bounded : ∀ n, structured n ∈ Icc (0 : ℝ) 1
  coefficient_bound : ∀ k n i, ‖coefficient k n i‖ ≤ 1
  approximation : ∀ δ > 0, ∃ k : ℕ, ∀ᶠ s in atTop,
    (∑ n ∈ Finset.range (N s),
      ‖(structured n : ℂ) - variableFrequencyPolynomial (coefficient k) (frequency k) n‖ ^ 2) /
        N s ≤ δ ^ 2
  control : ∀ W : ℕ → ℕ, (∀ᶠ s in atTop, 0 < W s) →
    Tendsto (fun s => (A s : ℝ) / W s) atTop (𝓝 0) →
    Tendsto (fun s => (W s : ℝ) / B s) atTop (𝓝 0) →
    Tendsto (fun s => (∑ n ∈ Finset.range (N s),
      windowFourierNorm (fun n => F n - structured n) n (W s)) / N s) atTop (𝓝 0) ∧
    (∀ k, Tendsto (fun s =>
      ((varyingPolynomialParameters (N s) (W s) (coefficient k) (frequency k)).card : ℝ) / N s)
        atTop (𝓝 0)) ∧
    ∀ k C : ℕ, 0 < C → Tendsto (fun s =>
      ((badFrequencyCombinationWindows (N s) (W s) C (frequency k)).card : ℝ) / N s)
        atTop (𝓝 0)

theorem exists_intermediate_fourier_model
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (F : ℕ → ℝ) (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ τ A B : ℕ → ℕ,
      StrictMono τ ∧ Tendsto (fun s => (N (τ (s - 1)) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      (∀ s, 0 < A s ∧ 0 < B s) ∧ Tendsto A atTop atTop ∧
      Tendsto (fun s => (lower (τ s) : ℝ) / A s) atTop (𝓝 0) ∧
      Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0) ∧
      Tendsto (fun s => (B s : ℝ) / upper (τ s)) atTop (𝓝 0) ∧
      Nonempty (IntermediateFourierModel F (N ∘ τ) A B) := by
  obtain ⟨τ, A, B, w, d, c, α, hτ, hp, hab, hat, hlo, hsep, hhi, hd, hc, hw,
    horth, hmean, happ, hcontrol⟩ :=
    exists_intermediate_fourier_decomposition N hN hmono hprev lower upper
      hlower hupper hgap hupperN F hF U hU
  exact ⟨τ, A, B, hτ, hp, hab, hat, hlo, hsep, hhi,
    ⟨{ structured := w, dimension := d, coefficient := c, frequency := α,
       bounded := hw, coefficient_bound := hc, approximation := happ, control := hcontrol }⟩⟩

def IntermediateFourierModel.restrict {F : ℕ → ℝ} {N A B : ℕ → ℕ}
    (m : IntermediateFourierModel F N A B)
    (hApos : ∀ s, 0 < A s) (hBpos : ∀ s, 0 < B s) (hA : Tendsto A atTop atTop)
    (hAB : Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (A' B' : ℕ → ℕ)
    (hA' : ∀ s, 0 < A' s) (hB' : ∀ s, 0 < B' s)
    (hlo : Tendsto (fun s => (A (σ s) : ℝ) / A' s) atTop (𝓝 0))
    (hhi : Tendsto (fun s => (B' s : ℝ) / B (σ s)) atTop (𝓝 0)) :
    IntermediateFourierModel F (N ∘ σ) A' B' where
  structured := m.structured
  dimension := m.dimension
  coefficient := m.coefficient
  frequency := m.frequency
  bounded := m.bounded
  coefficient_bound := m.coefficient_bound
  approximation := by
    intro δ hδ
    obtain ⟨k, hk⟩ := m.approximation δ hδ
    exact ⟨k, hσ.tendsto_atTop.eventually hk⟩
  control := by
    intro W hW hAW hWB
    have hAWold : Tendsto (fun s => (A (σ s) : ℝ) / W s) atTop (𝓝 0) :=
      window_ratio_tendsto_zero_of_intermediate W A' (A ∘ σ) hA' hlo hAW
    have hWBold : Tendsto (fun s => (W s : ℝ) / B (σ s)) atTop (𝓝 0) :=
      window_ratio_tendsto_zero_of_intermediate (B ∘ σ) B' W hB' hWB hhi
    refine ⟨?_, ?_, ?_⟩
    · exact tendsto_subsequence_of_intermediate_control A B hApos hBpos hA hAB
        (fun s L => (∑ n ∈ Finset.range (N s),
          windowFourierNorm (fun n => F n - m.structured n) n L) / N s)
        (fun V hV hAV hVB => (m.control V hV hAV hVB).1) σ hσ W hW hAWold hWBold
    · intro k
      exact tendsto_subsequence_of_intermediate_control A B hApos hBpos hA hAB
        (fun s L => ((varyingPolynomialParameters (N s) L (m.coefficient k) (m.frequency k)).card : ℝ) / N s)
        (fun V hV hAV hVB => (m.control V hV hAV hVB).2.1 k) σ hσ W hW hAWold hWBold
    · intro k C hC
      exact tendsto_subsequence_of_intermediate_control A B hApos hBpos hA hAB
        (fun s L => ((badFrequencyCombinationWindows (N s) L C (m.frequency k)).card : ℝ) / N s)
        (fun V hV hAV hVB => (m.control V hV hAV hVB).2.2 k C hC) σ hσ W hW hAWold hWBold

end Erdos335.IntermediateScale
