import Erdos335.OrdinaryFlatScaleDecomposition
import Erdos335.StitchedPolynomialLimit
import Erdos335.StitchedResidualLimit
import Erdos335.SubsequenceParameterDensity

/-!
# Intermediate-scale structure and uniformity for one ordinary bounded function

The polynomial parameters are locally constant outside a set of windows
of vanishing relative size. Frequency separation remains a further
scale-selection step.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_intermediate_block_decomposition
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (F : ℕ → ℝ) (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (Hminus Hplus : ℕ → ℕ) (ε : ℕ → ℝ) (L : ℕ → ℕ)
      (mminus : ∀ k s, BlockRegularModel F (Hminus s) (L k) (ε k))
      (mplus : ∀ k s, BlockRegularModel F (Hplus s) (L k) (ε k))
      (ρ : ℕ → ℕ) (w : ℕ → ℝ),
      (∀ s, 0 < Hminus s ∧ 0 < Hplus s) ∧
      Tendsto Hminus atTop atTop ∧
      Tendsto (fun s => (lower s : ℝ) / Hminus s) atTop (𝓝 0) ∧
      Tendsto (fun s => (Hminus s : ℝ) / Hplus s) atTop (𝓝 0) ∧
      Tendsto (fun s => (Hplus s : ℝ) / upper s) atTop (𝓝 0) ∧
      (∀ k, 0 < ε k ∧ ε k ≤ 1 ∧ 0 < L k) ∧
      Tendsto ε atTop (𝓝 0) ∧ StrictMono ρ ∧
      (∀ n, w n ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun s => prefixCorrelation w (fun n => F n - w n) (N (ρ s))) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixCorrelation (fun n => F n - w n) (fun _ => 1) (N (ρ s))) atTop (𝓝 0) ∧
      (∀ δ > 0, ∃ k : ℕ, ∀ᶠ s in atTop,
        (∑ n ∈ Finset.range (N (ρ s)), ‖(w n : ℂ) - stitchedBlockPolynomial N hN (mplus k) n‖ ^ 2) /
          N (ρ s) ≤ δ ^ 2) ∧
      ∀ W : ℕ → ℕ, (∀ᶠ s in atTop, 0 < W s) →
        Tendsto (fun s => (Hminus (ρ s) : ℝ) / W s) atTop (𝓝 0) →
        Tendsto (fun s => (W s : ℝ) / Hplus (ρ s)) atTop (𝓝 0) →
        Tendsto (fun s => (∑ n ∈ Finset.range (N (ρ s)),
          windowFourierNorm (fun n => F n - w n) n (W s)) / N (ρ s)) atTop (𝓝 0) ∧
        ∀ k, Tendsto (fun s => ((varyingParameterWindows N hN (mplus k) (ρ s) (W s)).card : ℝ) /
          N (ρ s)) atTop (𝓝 0) := by
  obtain ⟨ε, L, m, x, ρ, w, hx, hpos, hε, hρ, hw, hminus, hplus, horth, hmean⟩ :=
    exists_ordinary_flat_scale_decomposition N hN hmono hprev lower upper hlower hupper hgap hupperN F hF U hU
  let p : BlockScaleParameter := toLex (x, 0)
  let q : BlockScaleParameter := toLex (x, 1)
  let Hminus := blockScaleFamily lower upper p
  let Hplus := blockScaleFamily lower upper q
  have hminusPos := blockScaleFamily_pos lower upper p
  have hplusPos := blockScaleFamily_pos lower upper q
  have hplusN := blockScaleFamily_ambient_ratio lower upper N hlower hupper hgap hupperN q
  have hpq : p < q := Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, zero_lt_one⟩)
  refine ⟨Hminus, Hplus, ε, L, m p, m q, ρ, w,
    (fun s => ⟨hminusPos s, hplusPos s⟩), ?_, ?_, ?_, ?_, hpos, hε, hρ, hw, horth, hmean, ?_, ?_⟩
  · exact positiveIntermediateScale_atTop lower upper hlower hgap _ _ (blockScaleExponent_mem p).1
  · exact positiveIntermediateScale_lower_ratio lower upper hlower hgap _ _ (blockScaleExponent_mem p).1
  · exact blockScaleFamily_separated lower upper hlower hgap p q hpq
  · exact positiveIntermediateScale_ambient_ratio lower upper upper hlower hupper hgap
      (Eventually.of_forall fun _ => le_rfl) _ _ (blockScaleExponent_mem q).1 (blockScaleExponent_mem q).2
  · exact stitched_polynomial_approximation_of_limit N hN hmono hprev hplusPos hplusN (m q) ρ hρ w hε hplus
  · intro W hW hlow hhigh
    have hWN := window_ratio_tendsto_zero_of_intermediate (N ∘ ρ) (Hplus ∘ ρ) W
      (fun s => hplusPos (ρ s)) hhigh (hplusN.comp hρ.tendsto_atTop)
    constructor
    · exact stitched_residual_uniformity_of_limit N hN hmono hprev hminusPos (m p) hF ρ hρ w hw
        (fun k => (hpos k).1.le) (fun k => (hpos k).2.1) hε hminus W hW hlow hWN
    · exact fun k => varyingParameterWindows_density_along_subsequence N hN hmono (m q k)
        hplusPos ρ hρ W hprev hhigh hWN

end Erdos335.IntermediateScale
