import Erdos335.HighGapConvergentMacroSubsequence
import Erdos335.FiniteScalarStabilization

/-!
# Ordinary residue-section densities in the High branch

Private proof development. Verification status is recorded separately. The arbitrary-cutoff subsequence theorem
proves finite-template approximation for each coordinate. Canonical
normalized-prefix increment bounds and finite-template stabilization then
give ordinary convergence over all natural cutoffs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem exists_high_gap_ordinary_prefix_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b))
    (hgap : a + b < gamma A B)
    (hhighA : gamma A B < a + b + δA)
    (hhighB : gamma A B < a + b + δB)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (M : ℕ+)
    (hM : ∀ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 →
      (h : ℕ) ∣ (M : ℕ)) :
    ∃ vA vB : ZMod (M : ℕ) → ℝ,
      (∀ r, vA r ∈ positiveProfileScalarValues (M : ℕ) a) ∧
      (∀ r, vB r ∈ positiveProfileScalarValues (M : ℕ) b) ∧
      (∀ r, Tendsto (fun n => ((M : ℕ) : ℝ) *
        ((prefixCount {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r} n : ℝ) / n))
          atTop (𝓝 (vA r))) ∧
      (∀ r, Tendsto (fun n => ((M : ℕ) : ℝ) *
        ((prefixCount {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r} n : ℝ) / n))
          atTop (𝓝 (vB r))) ∧
      (∀ r, HasDensity {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r}
        (vA r / (M : ℕ))) ∧
      (∀ r, HasDensity {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r}
        (vB r / (M : ℕ))) := by
  classical
  have hcoordinate (side : Bool) (r : ZMod (M : ℕ)) :
      ∃ v ∈ positiveProfileScalarValues (M : ℕ) (if side then b else a),
        Tendsto (fun n => ((M : ℕ) : ℝ) *
          ((prefixCount {k : ℕ | k ∈ (if side then B else A) ∧
            (k : ZMod (M : ℕ)) = r} n : ℝ) / n)) atTop (𝓝 v) := by
    apply normalized_prefix_limit_of_finite_subsequence_limits
      {k : ℕ | k ∈ (if side then B else A) ∧ (k : ZMod (M : ℕ)) = r}
      ((M : ℕ) : ℝ) (by positivity)
      (positiveProfileScalarValues (M : ℕ) (if side then b else a))
    intro N0 hN0pos hN0
    obtain ⟨σ, vA, vB, hσ, _, _, hscalarA, hscalarB, hlimitA, hlimitB⟩ :=
      exists_high_gap_convergent_macro_subsequence U hU A B a b δA δB ha hb
        hAdensity hBdensity hCdensity hgap hhighA hhighB hcapA hcapB
          N0 hN0pos hN0 M hM
    cases side
    · exact ⟨σ, vA r, hσ, hscalarA r, hlimitA r⟩
    · exact ⟨σ, vB r, hσ, hscalarB r, hlimitB r⟩
  choose vA hscalarA hlimitA using fun r => hcoordinate false r
  choose vB hscalarB hlimitB using fun r => hcoordinate true r
  refine ⟨vA, vB, hscalarA, hscalarB, hlimitA, hlimitB, ?_, ?_⟩
  · intro r
    exact hasDensity_of_normalized_prefix_limit
      {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r}
      ((M : ℕ) : ℝ) (vA r) (by exact_mod_cast M.ne_zero) (hlimitA r)
  · intro r
    exact hasDensity_of_normalized_prefix_limit
      {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r}
      ((M : ℕ) : ℝ) (vB r) (by exact_mod_cast M.ne_zero) (hlimitB r)

end Erdos335.Loeb

end
