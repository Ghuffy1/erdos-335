import Erdos335.SparsePrefixSubsequence
import Erdos335.FixedScaleFourierModels
import Erdos335.JointResiduePrefixSubsequence
import Erdos335.HighGapMacroProfiles
import Erdos335.HighGapPrefixScalarValues

/-!
# Convergent macro subsequences in the High branch

Private proof development. Verification status is recorded separately. Arbitrary diverging positive cutoffs first
have a sparse increasing subsequence. Fixed-scale Fourier models and joint
compact extraction then retain the same scale through macro averaging.
The limit coordinates are realized by actual positive local profiles and
therefore belong to explicit finite scalar sets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem exists_high_gap_convergent_macro_subsequence
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
    (N0 : ℕ → ℕ) (hN0pos : ∀ s, 0 < N0 s) (hN0 : Tendsto N0 atTop atTop)
    (M : ℕ+)
    (hM : ∀ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 →
      (h : ℕ) ∣ (M : ℕ)) :
    ∃ (σ : ℕ → ℕ) (vA vB : ZMod (M : ℕ) → ℝ),
      StrictMono σ ∧
      (∀ r, vA r ∈ Set.Icc (0 : ℝ) ((M : ℕ) : ℝ)) ∧
      (∀ r, vB r ∈ Set.Icc (0 : ℝ) ((M : ℕ) : ℝ)) ∧
      (∀ r, vA r ∈ positiveProfileScalarValues (M : ℕ) a) ∧
      (∀ r, vB r ∈ positiveProfileScalarValues (M : ℕ) b) ∧
      (∀ r, Tendsto (fun s => ((M : ℕ) : ℝ) *
        ((prefixCount {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r} (N0 (σ s)) : ℝ) /
          N0 (σ s))) atTop (𝓝 (vA r))) ∧
      (∀ r, Tendsto (fun s => ((M : ℕ) : ℝ) *
        ((prefixCount {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r} (N0 (σ s)) : ℝ) /
          N0 (σ s))) atTop (𝓝 (vB r))) := by
  classical
  obtain ⟨ρ, hρ, hNρ, hprev⟩ := exists_sparse_prefix_subsequence N0 hN0
  let N1 : ℕ → ℕ := N0 ∘ ρ
  letI : ∀ s, NeZero (N1 s) := fun s => ⟨(hN0pos (ρ s)).ne'⟩
  have hN1 : Tendsto N1 atTop atTop := hN0.comp hρ.tendsto_atTop
  obtain ⟨τ, L, V, H, hτ, _, hpos, hHpos, hL, hH, hLV, hLH, hHV, hHN,
      hAerror, hBerror, hCerror, ⟨mA⟩, ⟨mB⟩⟩ :=
    exists_fixed_scale_fourier_models_of_density N1 hN1 hNρ.monotone hprev
      A B a b (a + b) hAdensity hBdensity hCdensity U hU
  obtain ⟨κ, vA, vB, hκ, hvA, hvB, hprefixA, hprefixB⟩ :=
    exists_joint_residue_prefix_subsequence A B M H hHpos
  let N2 : ℕ → ℕ := (N1 ∘ τ) ∘ κ
  have hN2pos : ∀ s, 0 < N2 s := fun s => hN0pos (ρ (τ (κ s)))
  let mA' := mA.subsequence (fun s => (hpos s).1) (fun s => (hpos s).2) hL hLV κ hκ
  let mB' := mB.subsequence (fun s => (hpos s).1) (fun s => (hpos s).2) hL hLV κ hκ
  have hmacro := high_gap_macro_prefix_profiles U hU A B a b δA δB ha hb
    hAdensity hBdensity hCdensity hgap hhighA hhighB hcapA hcapB
      N2 (L ∘ κ) (V ∘ κ) (H ∘ κ) hN2pos
        (fun s => (hpos (κ s)).1) (fun s => (hpos (κ s)).2)
          (hL.comp hκ.tendsto_atTop) (hLV.comp hκ.tendsto_atTop)
            (fun s => hHpos (κ s)) (hH.comp hκ.tendsto_atTop)
              (hLH.comp hκ.tendsto_atTop) (hHV.comp hκ.tendsto_atTop)
                (hHN.comp hκ.tendsto_atTop) mA' mB'
                  (hAerror.comp hκ.tendsto_atTop) (hBerror.comp hκ.tendsto_atTop)
                    (hCerror.comp hκ.tendsto_atTop) M hM vA vB hprefixA hprefixB
  obtain ⟨_, _, hscalarA, hscalarB⟩ := high_gap_prefix_scalar_values U hU A B a b δA δB
    ha hb hAdensity hBdensity hCdensity hgap hhighA hhighB hcapA hcapB
      N2 (L ∘ κ) (V ∘ κ) (H ∘ κ) hN2pos
        (fun s => hHpos (κ s)) (hH.comp hκ.tendsto_atTop)
          (hLH.comp hκ.tendsto_atTop) (hHV.comp hκ.tendsto_atTop)
            (hHN.comp hκ.tendsto_atTop) mA' mB'
              (hAerror.comp hκ.tendsto_atTop) (hBerror.comp hκ.tendsto_atTop)
                (hCerror.comp hκ.tendsto_atTop) M hM vA vB hprefixA hprefixB
  refine ⟨ρ ∘ τ ∘ κ, vA, vB, hρ.comp (hτ.comp hκ), hvA, hvB,
    hscalarA, hscalarB, ?_, ?_⟩
  · simpa only [N2, N1, Function.comp_def] using hmacro.1
  · simpa only [N2, N1, Function.comp_def] using hmacro.2

end Erdos335.Loeb

end
