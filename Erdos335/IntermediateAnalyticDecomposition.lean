import Erdos335.IntermediateConvolutionPeriods

/-!
# An ordinary intermediate decomposition with convolution transfer and periods
-/

set_option autoImplicit false

open Filter Topology Set
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_intermediate_analytic_decomposition
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (F : ℕ → ℝ) (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (τ A B : ℕ → ℕ) (w : ℕ → ℝ),
      StrictMono τ ∧
      Tendsto (fun s => (N (τ (s - 1)) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      (∀ s, 0 < A s ∧ 0 < B s) ∧ Tendsto A atTop atTop ∧
      Tendsto (fun s => (lower (τ s) : ℝ) / A s) atTop (𝓝 0) ∧
      Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0) ∧
      Tendsto (fun s => (B s : ℝ) / upper (τ s)) atTop (𝓝 0) ∧
      (∀ n, w n ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun s => prefixCorrelation w (fun n => F n - w n) (N (τ s))) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixCorrelation (fun n => F n - w n) (fun _ => 1) (N (τ s))) atTop (𝓝 0) ∧
      ∀ H : ℕ → ℕ, (∀ s, 0 < H s) →
        Tendsto (fun s => (A s : ℝ) / H s) atTop (𝓝 0) →
        Tendsto (fun s => (H s : ℝ) / B s) atTop (𝓝 0) →
        ∀ R : ℕ, 0 < R →
          (∀ g : ℕ → ℕ → ℂ, (∀ s n, ‖g s n‖ ≤ 1) →
            Tendsto (fun s => (∑ n ∈ Finset.range (N (τ s)),
              ‖linearWindowConvolution F (g s) (H s) n -
                linearWindowConvolution w (g s) (H s) n‖ ^ 2) / N (τ s)) atTop (𝓝 0)) ∧
          ∃ (Q : ℕ → ℕ → ℕ) (ε : ℕ → ℝ),
            (∀ s, 0 < ε s) ∧ Tendsto ε atTop (𝓝 0) ∧
            (∀ᶠ s in atTop, ∀ n, H s ≤ Q s n ∧ (Q s n : ℝ) ≤ (1 + ε s) * H s) ∧
            (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, ∀ n, M ∣ Q s n) ∧
            Tendsto (fun s => averagedWindowTranslationError (fun n => (w n : ℂ))
              (Q s) (N (τ s)) (R * H s)) atTop (𝓝 0) := by
  obtain ⟨τ, A, B, w, d, c, α, hτ, hprev', hAB, hA, hlo, hABlim, hhi,
    hd, hc, hw, horth, hmean, happrox, hcontrol⟩ :=
    exists_intermediate_fourier_decomposition N hN hmono hprev lower upper hlower hupper hgap hupperN F hF U hU
  refine ⟨τ, A, B, w, hτ, hprev', hAB, hA, hlo, hABlim, hhi, hw, horth, hmean, ?_⟩
  intro H hHpos hAH hHB R hR
  have hH : Tendsto H atTop atTop :=
    scale_tendsto_atTop_of_smaller A H hA hHpos hAH
  have hNpos (s : ℕ) : 0 < N (τ s) := NeZero.pos _
  have hUpos : ∀ᶠ s in atTop, 0 < upper (τ s) :=
    (hupper.comp hτ.tendsto_atTop).eventually (eventually_gt_atTop 0)
  have hUN : ∀ᶠ s in atTop, upper (τ s) ≤ N (τ s) := hτ.tendsto_atTop.eventually hupperN
  have hBN : Tendsto (fun s => (B s : ℝ) / N (τ s)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hhi
    filter_upwards [hUpos, hUN] with s hs hbound
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hs)
      (by exact_mod_cast hbound)
  have hHN : Tendsto (fun s => (H s : ℝ) / N (τ s)) atTop (𝓝 0) := by
    have h := hHB.mul hBN
    have heq (s : ℕ) : (H s : ℝ) / B s * ((B s : ℝ) / N (τ s)) =
        (H s : ℝ) / N (τ s) := by
      have hb : (B s : ℝ) ≠ 0 := by exact_mod_cast (hAB s).2.ne'
      field_simp
    simpa only [heq, mul_zero] using h
  exact intermediate_fourier_convolution_and_periods R hR F w hF hw d c α hc
    (N ∘ τ) A B hNpos happrox
    (fun W hW hAW hWB => hcontrol W (Eventually.of_forall hW) hAW hWB)
    H hHpos hH hAH hHB hHN

end Erdos335.IntermediateScale
