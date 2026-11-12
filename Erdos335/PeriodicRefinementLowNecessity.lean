import Erdos335.PeriodicRefinementPreparedWindows
import Erdos335.PeriodicRefinementPeriodicRecovery
import Erdos335.SparsePrefixSubsequence

/-!
# An ordinary periodic summand in the Low branch
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale Erdos335.PeriodicRefinementLabelClosure
open Erdos335.PeriodicRefinementMacroAssembly
open scoped Pointwise

noncomputable section

namespace Erdos335.PeriodicRefinement

theorem raw_macro_profile_at_prefix_cluster
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hlowA : ∀ η : ℝ, gamma A B - (a + b) < η →
      ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η)
    (hcapA : ∀ k : ℕ+, a + δA ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ))
    (hcapB : ∀ k : ℕ+, b + δB ≤ ((residues (k : ℕ) B).card : ℝ) / (k : ℕ))
    (D : ℕ)
    (hD : max (1 / δA) (max (1 / δB) (1 / (gamma A B - (a + b)))) ≤ (D : ℝ))
    (v : ProfilePair (ZMod D.factorial))
    (hv : MapClusterPt v atTop
      (residuePrefixPair A B ⟨D.factorial, Nat.factorial_pos D⟩)) :
    ∃ raw : RawMacroProfileData (residues D.factorial A) (residues D.factorial B)
        ((D.factorial : ℝ) * a) ((D.factorial : ℝ) * b), raw.endpoint = v := by
  classical
  let M : ℕ+ := ⟨D.factorial, Nat.factorial_pos D⟩
  obtain ⟨σ0, hσ0, hlimit⟩ := hv.tendsto_subseq
  let N0 : ℕ → ℕ := fun n => σ0 (n + 1)
  have hN0positive (n : ℕ) : 0 < N0 n := by
    dsimp only [N0]
    exact (Nat.zero_le (σ0 0)).trans_lt (hσ0 (Nat.zero_lt_succ n))
  have hN0 : Tendsto N0 atTop atTop :=
    hσ0.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hlimit0 : Tendsto (fun n => residuePrefixPair A B M (N0 n)) atTop (𝓝 v) :=
    hlimit.comp (tendsto_add_atTop_nat 1)
  obtain ⟨ρ, hρ, hNρ, hprevious⟩ := exists_sparse_prefix_subsequence N0 hN0
  let N1 := N0 ∘ ρ
  have hN1positive (n : ℕ) : 0 < N1 n := hN0positive (ρ n)
  have hN1 : Tendsto N1 atTop atTop := hN0.comp hρ.tendsto_atTop
  obtain ⟨σ1, prepared, hσ1, hprepared⟩ := exists_prepared_macro_scales A B a b M
    hAdensity hBdensity hCdensity N1 hN1positive hN1 hNρ.monotone hprevious
  obtain ⟨σ2, data, hσ2, hdata, _⟩ := prepared.exists_window_sequence
  have hdataCutoff : data.cutoff = N1 ∘ σ1 ∘ σ2 := by
    rw [hdata, hprepared]
    rfl
  have hpairLimit : Tendsto (fun n => residuePrefixPair A B M (data.cutoff n))
      atTop (𝓝 v) := by
    rw [hdataCutoff]
    exact ((hlimit0.comp hρ.tendsto_atTop).comp hσ1.tendsto_atTop).comp hσ2.tendsto_atTop
  obtain ⟨raw, hleft, hright⟩ := macroWindowSequence_rawData A B a b δA δB
    ha hb hδA hδB hAdensity hBdensity hCdensity hgap hlowA hcapA hcapB D hD data
  have hendpoint : Tendsto (fun n => residuePrefixPair A B M (data.cutoff n))
      atTop (𝓝 raw.endpoint) := by
    rw [RawMacroProfileData.endpoint, hleft, hright]
    apply Tendsto.prodMk_nhds
    · apply tendsto_pi_nhds.mpr
      intro r
      simpa [residuePrefixPair, macroInput, M] using data.endpoint_prefix_tendsto 0 r
    · apply tendsto_pi_nhds.mpr
      intro r
      simpa [residuePrefixPair, macroInput, M] using data.endpoint_prefix_tendsto 1 r
  exact ⟨raw, tendsto_nhds_unique hendpoint hpairLimit⟩

end Erdos335.PeriodicRefinement

namespace Erdos335.Proposed

theorem low_periodic_summand_necessity : LowPeriodicSummandNecessity := by
  classical
  intro A B a b δA δB hApos hBpos ha hb hAdensity hBdensity hCdensity hgap
    hδA hδB hcapA hcapB hlow
  obtain ⟨D, hD⟩ := exists_nat_ge
    (max (1 / δA) (max (1 / δB) (1 / (gamma A B - (a + b)))))
  let M : ℕ+ := ⟨D.factorial, Nat.factorial_pos D⟩
  have hM : (0 : ℝ) < (M : ℕ) := by exact_mod_cast M.pos
  have hfiniteGap : ((M : ℕ) : ℝ) * a + ((M : ℕ) : ℝ) * b <
      ((residues (M : ℕ) A + residues (M : ℕ) B).card : ℝ) := by
    have h := hgap.trans_le (gamma_le_modularCapacity A B M)
    change a + b < ((residues (M : ℕ) A + residues (M : ℕ) B).card : ℝ) / (M : ℕ) at h
    have hmul := (lt_div_iff₀ hM).mp h
    nlinarith
  have hmacro : ∀ v, MapClusterPt v atTop (PeriodicRefinement.residuePrefixPair A B M) →
      ∃ raw : RawMacroProfileData (residues (M : ℕ) A) (residues (M : ℕ) B)
        (((M : ℕ) : ℝ) * a) (((M : ℕ) : ℝ) * b), raw.endpoint = v := by
    intro v hv
    exact PeriodicRefinement.raw_macro_profile_at_prefix_cluster A B a b δA δB
      ha hb hδA hδB hAdensity hBdensity hCdensity hgap hlow hcapA hcapB D hD v hv
  obtain hleft | hright := exists_periodic_coordinate_limit_of_raw_cluster_profiles
    (PeriodicRefinement.residuePrefixPair A B M) (PeriodicRefinement.prefixProfileCompact M)
    (mul_pos hM ha) (mul_pos hM hb) hfiniteGap
    (PeriodicRefinement.isCompact_prefixProfileCompact M)
    (Eventually.of_forall fun n => PeriodicRefinement.residuePrefixPair_mem_compact A B M n)
    (PeriodicRefinement.residuePrefixPair_step A B M) hmacro
    (PeriodicRefinement.prefix_pair_cluster_localProfile A B M a b hAdensity hBdensity hCdensity)
  · obtain ⟨P, hP⟩ := hleft
    exact ⟨M, P, Or.inl (PeriodicRefinement.periodic_of_residue_prefix_mask A M a hApos hAdensity P hP)⟩
  · obtain ⟨Q, hQ⟩ := hright
    exact ⟨M, Q, Or.inr (PeriodicRefinement.periodic_of_residue_prefix_mask B M b hBpos hBdensity Q hQ)⟩

end Erdos335.Proposed

end
