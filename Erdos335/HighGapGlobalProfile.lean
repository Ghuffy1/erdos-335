import Erdos335.HighGapAllResidueDensities
import Erdos335.HighGapOrdinaryReferenceProfile
import Erdos335.SparsePrefixSubsequence
import Erdos335.FixedScaleFourierModels

/-!
# One High-branch positive profile for every ordinary refinement

Private proof development. Verification status is recorded separately. A single actual paired model supplies the
finite parameters. Ordinary zero-prefix densities identify all of its
input profiles, including every refinement of its bounded modulus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem exists_high_gap_global_positive_profile
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
    ∃ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 ∧
      ∃ fA fB output : NaturalResidueProfile,
      ∃ p : LocalPositiveResidueProfile h A B a b fA fB output,
        p.movingSupport = residues (h : ℕ) A ∧
        (∀ (m : ℕ+) (r : ZMod (m : ℕ)), HasDensity {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
          (fA m r / (m : ℕ))) ∧
        (∀ (m : ℕ+) (r : ZMod (m : ℕ)), HasDensity {n : ℕ | n ∈ B ∧ (n : ZMod (m : ℕ)) = r}
          (fB m r / (m : ℕ))) ∧
        (∀ m : ℕ+, (h : ℕ) ∣ (m : ℕ) → ∀ r : ZMod (m : ℕ),
          HasDensity {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
            (positiveResiduePattern h (residues (h : ℕ) A) p.activeMoving p.movingMass m r /
              (m : ℕ)) ∧
          HasDensity {n : ℕ | n ∈ B ∧ (n : ZMod (m : ℕ)) = r}
            (positiveResiduePattern h (residues (h : ℕ) B) p.activePrefix p.prefixMass m r /
              (m : ℕ))) := by
  classical
  obtain ⟨fA, fB, hfA, hfB⟩ := exists_high_gap_all_residue_densities U hU A B a b δA δB
    ha hb hAdensity hBdensity hCdensity hgap hhighA hhighB hcapA hcapB M hM
  let N0 : ℕ → ℕ := fun n => n + 1
  have hN0 : Tendsto N0 atTop atTop := tendsto_add_atTop_nat 1
  obtain ⟨ρ, hρ, hNρ, hprev⟩ := exists_sparse_prefix_subsequence N0 hN0
  let N1 : ℕ → ℕ := N0 ∘ ρ
  have hN1pos : ∀ s, 0 < N1 s := fun s => Nat.succ_pos (ρ s)
  letI : ∀ s, NeZero (N1 s) := fun s => ⟨(hN1pos s).ne'⟩
  have hN1 : Tendsto N1 atTop atTop := hN0.comp hρ.tendsto_atTop
  obtain ⟨τ, L, V, H, _, _, _, hHpos, _, hH, _, hLH, hHV, hHN,
      hAerror, hBerror, hCerror, ⟨mA⟩, ⟨mB⟩⟩ :=
    exists_fixed_scale_fourier_models_of_density N1 hN1 hNρ.monotone hprev
      A B a b (a + b) hAdensity hBdensity hCdensity U hU
  obtain ⟨h, hbound, output, p, hSA⟩ :=
    exists_high_gap_profile_of_ordinary_residue_densities U hU A B a b δA δB
      ha hb hAdensity hBdensity hCdensity hgap hhighA hhighB hcapA hcapB
        (N1 ∘ τ) L V H (fun s => hN1pos (τ s)) hHpos hH hLH hHV hHN mA mB
          hAerror hBerror hCerror fA fB hfA hfB
  refine ⟨h, hbound, fA, fB, output, p, hSA, hfA, hfB, ?_⟩
  intro m hm r
  constructor
  · have hp := p.moving_profile m hm r
    rw [hSA] at hp
    simpa only [hp] using hfA m r
  · simpa only [p.prefix_profile m hm r] using hfB m r

end Erdos335.Loeb

end
