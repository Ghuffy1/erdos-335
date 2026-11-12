import Erdos335.OrdinaryFlatScaleDecomposition
import Erdos335.StitchedPolynomialLimit
import Erdos335.StitchedResidualLimit
import Erdos335.SubsequenceParameterDensity
import Erdos335.PolynomialParameterModels
import Erdos335.SparseScaleSubsequence
import Erdos335.PolynomialFrequencySelection
import Erdos335.ReciprocalScaleRatios

/-!
# Intermediate-scale Fourier decomposition with separated polynomial frequencies

The bounded ordinary representative, polynomial structure, local parameter
constancy and simultaneous frequency selection use a common subsequence.
-/

set_option autoImplicit false

open Filter Topology Set
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_intermediate_fourier_decomposition
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (F : ℕ → ℝ) (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (τ A B : ℕ → ℕ) (w : ℕ → ℝ) (L : ℕ → ℕ)
      (c : ∀ k, ℕ → Fin (L k) → ℂ) (α : ∀ k, ℕ → Fin (L k) → ℝ),
      StrictMono τ ∧
      Tendsto (fun s => (N (τ (s - 1)) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      (∀ s, 0 < A s ∧ 0 < B s) ∧ Tendsto A atTop atTop ∧
      Tendsto (fun s => (lower (τ s) : ℝ) / A s) atTop (𝓝 0) ∧
      Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0) ∧
      Tendsto (fun s => (B s : ℝ) / upper (τ s)) atTop (𝓝 0) ∧
      (∀ k, 0 < L k) ∧ (∀ k n j, ‖c k n j‖ ≤ 1) ∧
      (∀ n, w n ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun s => prefixCorrelation w (fun n => F n - w n) (N (τ s))) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixCorrelation (fun n => F n - w n) (fun _ => 1) (N (τ s))) atTop (𝓝 0) ∧
      (∀ δ > 0, ∃ k : ℕ, ∀ᶠ s in atTop,
        (∑ n ∈ Finset.range (N (τ s)), ‖(w n : ℂ) - variableFrequencyPolynomial (c k) (α k) n‖ ^ 2) /
          N (τ s) ≤ δ ^ 2) ∧
      ∀ W : ℕ → ℕ, (∀ᶠ s in atTop, 0 < W s) →
        Tendsto (fun s => (A s : ℝ) / W s) atTop (𝓝 0) →
        Tendsto (fun s => (W s : ℝ) / B s) atTop (𝓝 0) →
        Tendsto (fun s => (∑ n ∈ Finset.range (N (τ s)),
          windowFourierNorm (fun n => F n - w n) n (W s)) / N (τ s)) atTop (𝓝 0) ∧
        (∀ k, Tendsto (fun s => ((varyingPolynomialParameters (N (τ s)) (W s) (c k) (α k)).card : ℝ) /
          N (τ s)) atTop (𝓝 0)) ∧
        ∀ k C : ℕ, 0 < C → Tendsto
          (fun s => ((badFrequencyCombinationWindows (N (τ s)) (W s) C (α k)).card : ℝ) / N (τ s))
          atTop (𝓝 0) := by
  obtain ⟨ε, L, m, x, ρ, w, _hx, hpos, hε, hρ, hw, hminus, hplus, horth, hmean⟩ :=
    exists_ordinary_flat_scale_decomposition N hN hmono hprev lower upper hlower hupper hgap hupperN F hF U hU
  let p : BlockScaleParameter := toLex (x, 0)
  let q : BlockScaleParameter := toLex (x, 1)
  let Hminus := blockScaleFamily lower upper p
  let Hplus := blockScaleFamily lower upper q
  let c := fun k => stitchedBlockCoefficient N hN (m q k)
  let α := fun k => stitchedBlockFrequency N hN (m q k)
  have hminusPos := blockScaleFamily_pos lower upper p
  have hplusPos := blockScaleFamily_pos lower upper q
  have hminusTop : Tendsto Hminus atTop atTop :=
    positiveIntermediateScale_atTop lower upper hlower hgap _ _ (blockScaleExponent_mem p).1
  have hpq : p < q := Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, zero_lt_one⟩)
  have hsep : Tendsto (fun s => (Hminus s : ℝ) / Hplus s) atTop (𝓝 0) :=
    blockScaleFamily_separated lower upper hlower hgap p q hpq
  have hplusTop := scale_tendsto_atTop_of_smaller Hminus Hplus hminusTop hplusPos hsep
  have hreverse := reciprocal_scale_ratio_tendsto_atTop Hminus Hplus hminusPos hplusPos hsep
  have hlow : Tendsto (fun s => (lower s : ℝ) / Hminus s) atTop (𝓝 0) :=
    positiveIntermediateScale_lower_ratio lower upper hlower hgap _ _ (blockScaleExponent_mem p).1
  have hhigh : Tendsto (fun s => (Hplus s : ℝ) / upper s) atTop (𝓝 0) :=
    positiveIntermediateScale_ambient_ratio lower upper upper hlower hupper hgap
      (Eventually.of_forall fun _ => le_rfl) _ _ (blockScaleExponent_mem q).1 (blockScaleExponent_mem q).2
  have hplusN := blockScaleFamily_ambient_ratio lower upper N hlower hupper hgap hupperN q
  letI : ∀ s, NeZero ((N ∘ ρ) s) := fun s => inferInstanceAs (NeZero (N (ρ s)))
  obtain ⟨A₀, B₀, σ, hσ, hABpos, hsmall, hAB, hlarge, hfrequency⟩ :=
    exists_polynomial_frequency_scale_selection (N ∘ ρ) (Hminus ∘ ρ) (Hplus ∘ ρ)
      (hminusTop.comp hρ.tendsto_atTop) (hplusTop.comp hρ.tendsto_atTop)
      (hreverse.comp hρ.tendsto_atTop) U hU L α
  let τ := ρ ∘ σ
  let A := A₀ ∘ σ
  let B := B₀ ∘ σ
  have hτ : StrictMono τ := hρ.comp hσ
  have hApos (s : ℕ) : 0 < A s := (hABpos (σ s)).1
  have hBpos (s : ℕ) : 0 < B s := (hABpos (σ s)).2
  have hsmall' : Tendsto (fun s => (Hminus (τ s) : ℝ) / A s) atTop (𝓝 0) :=
    hsmall.comp hσ.tendsto_atTop
  have hlarge' : Tendsto (fun s => (B s : ℝ) / Hplus (τ s)) atTop (𝓝 0) :=
    hlarge.comp hσ.tendsto_atTop
  have hminus' : ∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
      prefixEnergy (fun n => w n - stitchedBlockValue N hN (m p k) n) (N (τ s)) ≤ δ := by
    intro δ hδ
    obtain ⟨K, hK⟩ := hminus δ hδ
    exact ⟨K, fun k hk => hσ.tendsto_atTop.eventually (hK k hk)⟩
  have hplus' : ∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
      prefixEnergy (fun n => w n - stitchedBlockValue N hN (m q k) n) (N (τ s)) ≤ δ := by
    intro δ hδ
    obtain ⟨K, hK⟩ := hplus δ hδ
    exact ⟨K, fun k hk => hσ.tendsto_atTop.eventually (hK k hk)⟩
  refine ⟨τ, A, B, w, L, c, α, hτ, sparse_prefix_ratio_subsequence N hmono hprev τ hτ,
    (fun s => ⟨hApos s, hBpos s⟩), ?_, ?_, ?_, ?_,
    (fun k => (hpos k).2.2), ?_, hw, horth.comp hσ.tendsto_atTop, hmean.comp hσ.tendsto_atTop, ?_, ?_⟩
  · exact (scale_tendsto_atTop_of_smaller (Hminus ∘ ρ) A₀
      (hminusTop.comp hρ.tendsto_atTop) (fun s => (hABpos s).1) hsmall).comp hσ.tendsto_atTop
  · exact window_ratio_tendsto_zero_of_intermediate A (Hminus ∘ τ) (lower ∘ τ)
      (fun s => hminusPos (τ s)) (hlow.comp hτ.tendsto_atTop) hsmall'
  · exact hAB.comp hσ.tendsto_atTop
  · exact window_ratio_tendsto_zero_of_intermediate (upper ∘ τ) (Hplus ∘ τ) B
      (fun s => hplusPos (τ s)) hlarge' (hhigh.comp hτ.tendsto_atTop)
  · exact fun k n j => stitchedBlockCoefficient_bound N hN (m q k) n j
  · simpa only [c, α, variableFrequencyPolynomial_stitched] using
      stitched_polynomial_approximation_of_limit N hN hmono hprev hplusPos hplusN (m q) τ hτ w hε hplus'
  · intro W hW hAW hWB
    have hlowW := window_ratio_tendsto_zero_of_intermediate W A (Hminus ∘ τ) hApos hsmall' hAW
    have hhighW := window_ratio_tendsto_zero_of_intermediate (Hplus ∘ τ) B W hBpos hWB hlarge'
    have hWN := window_ratio_tendsto_zero_of_intermediate (N ∘ τ) (Hplus ∘ τ) W
      (fun s => hplusPos (τ s)) hhighW (hplusN.comp hτ.tendsto_atTop)
    refine ⟨?_, ?_, ?_⟩
    · exact stitched_residual_uniformity_of_limit N hN hmono hprev hminusPos (m p) hF τ hτ w hw
        (fun k => (hpos k).1.le) (fun k => (hpos k).2.1) hε hminus' W hW hlowW hWN
    · intro k
      simpa only [c, α, varyingPolynomialParameters_stitched] using
        varyingParameterWindows_density_along_subsequence N hN hmono (m q k) hplusPos τ hτ W hprev hhighW hWN
    · exact hfrequency W hW hAW hWB

end Erdos335.IntermediateScale
