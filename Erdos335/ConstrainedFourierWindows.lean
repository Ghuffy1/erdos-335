import Erdos335.FourierModelPeriodData
import Erdos335.ConstrainedConvolutionWindows

/-!
# Fourier-controlled windows inside prescribed dense sets of starts
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335.IntermediateScale

theorem exists_constrained_fourier_windows {I : Type*} [Fintype I]
    (A B : I → Set ℕ) (N L V H : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (hHpos : ∀ s, 0 < H s) (hH : Tendsto H atTop atTop)
    (hLH : Tendsto (fun s => (L s : ℝ) / H s) atTop (𝓝 0))
    (hHV : Tendsto (fun s => (H s : ℝ) / V s) atTop (𝓝 0))
    (hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (m : ∀ i, IntermediateFourierModel ((A i).indicator (fun _ => (1 : ℝ))) N L V)
    (S : ℕ → Finset ℕ) (hS : ∀ s, S s ⊆ Finset.range (N s))
    (δ : ℝ) (hδ : 0 < δ) (hcard : ∀ᶠ s in atTop, δ ≤ ((S s).card : ℝ) / N s) :
    ∃ (n : ℕ → ℕ) (q : I → ℕ → ℕ+),
      (∀ s, n s < N s) ∧ (∀ᶠ s in atTop, n s ∈ S s) ∧ ∀ i,
      (∀ s, H s ≤ (q i s : ℕ)) ∧ Tendsto (fun s => (q i s : ℕ)) atTop atTop ∧
      Tendsto (fun s => (((q i s : ℕ) - H s : ℕ) : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q i s : ℕ)) ∧
      (∀ᶠ s in atTop, n s + 3 * H s + (q i s : ℕ) ≤ N s) ∧
      Tendsto (fun s => convolutionTranslationError (A i) (B i) (n s + 3 * H s) (q i s : ℕ) /
        ((q i s : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  classical
  have hF (i : I) (n : ℕ) : (A i).indicator (fun _ => (1 : ℝ)) n ∈ Icc (0 : ℝ) 1 := by
    by_cases hn : n ∈ A i <;> simp [hn]
  have hdata (i : I) := exists_fourier_model_period_data (m i) (hF i) hN H hHpos hH hLH hHV hHN
  choose Q ε hεpos hεlim hQ hdiv hperiod hFourier using hdata
  exact exists_joint_convolution_windows_in_dense_sets A B (fun i => (m i).structured) N H hN hHpos
    hH hHN Q ε (fun i s => (hεpos i s).le) hεlim hQ hdiv hFourier hperiod S hS δ hδ hcard

end Erdos335.IntermediateScale
