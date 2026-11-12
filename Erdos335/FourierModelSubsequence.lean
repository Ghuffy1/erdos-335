import Erdos335.IntermediateFourierModel

/-!
# Preserving Fourier witnesses under a strict subsequence
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace Erdos335.IntermediateScale

def IntermediateFourierModel.subsequence {F : ℕ → ℝ} {N L V : ℕ → ℕ}
    (m : IntermediateFourierModel F N L V)
    (hLpos : ∀ s, 0 < L s) (hVpos : ∀ s, 0 < V s)
    (hL : Tendsto L atTop atTop)
    (hLV : Tendsto (fun s => (L s : ℝ) / V s) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    IntermediateFourierModel F (N ∘ σ) (L ∘ σ) (V ∘ σ) where
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
    intro W hW hLW hWV
    refine ⟨?_, ?_, ?_⟩
    · exact tendsto_subsequence_of_intermediate_control L V hLpos hVpos hL hLV
        (fun s R => (∑ n ∈ Finset.range (N s),
          windowFourierNorm (fun n => F n - m.structured n) n R) / N s)
        (fun R hR hLR hRV => (m.control R hR hLR hRV).1) σ hσ W hW hLW hWV
    · intro k
      exact tendsto_subsequence_of_intermediate_control L V hLpos hVpos hL hLV
        (fun s R => ((varyingPolynomialParameters (N s) R (m.coefficient k) (m.frequency k)).card : ℝ) / N s)
        (fun R hR hLR hRV => (m.control R hR hLR hRV).2.1 k) σ hσ W hW hLW hWV
    · intro k C hC
      exact tendsto_subsequence_of_intermediate_control L V hLpos hVpos hL hLV
        (fun s R => ((badFrequencyCombinationWindows (N s) R C (m.frequency k)).card : ℝ) / N s)
        (fun R hR hLR hRV => (m.control R hR hLR hRV).2.2 k C hC) σ hσ W hW hLW hWV

end Erdos335.IntermediateScale
