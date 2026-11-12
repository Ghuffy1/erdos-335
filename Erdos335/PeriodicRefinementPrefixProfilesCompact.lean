import Erdos335.PeriodicRefinementPrefixProfiles
import Erdos335.FiniteScalarStabilization
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact prefix pairs and actual local profiles at their cluster points

Private proof development. Verification status is recorded separately.
The output vector is extracted on a further subsequence of the two given
input limits. Every local-profile field follows from ordinary counts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open Erdos335.PeriodicRefinementLabelClosure
open scoped Pointwise

noncomputable section

namespace Erdos335.PeriodicRefinement

def residuePrefixPair (A B : Set ℕ) (M : ℕ+) (N : ℕ) :
    (ZMod (M : ℕ) → ℝ) × (ZMod (M : ℕ) → ℝ) :=
  (normalizedResiduePrefix A M N, normalizedResiduePrefix B M N)

def prefixProfileCompact (M : ℕ+) :
    Set ((ZMod (M : ℕ) → ℝ) × (ZMod (M : ℕ) → ℝ)) :=
  (Set.pi Set.univ (fun _ => Icc (0 : ℝ) ((M : ℕ) : ℝ))) ×ˢ
    (Set.pi Set.univ (fun _ => Icc (0 : ℝ) ((M : ℕ) : ℝ)))

theorem normalized_residue_prefix_bound (A : Set ℕ) (M : ℕ+) (N : ℕ)
    (r : ZMod (M : ℕ)) :
    normalizedResiduePrefix A M N r ∈ Icc (0 : ℝ) ((M : ℕ) : ℝ) := by
  refine ⟨normalized_residue_prefix_nonneg A M N r, ?_⟩
  by_cases hN : N = 0
  · simp only [normalizedResiduePrefix, hN, Nat.cast_zero, div_zero, mul_zero]
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hratio : (prefixCount (literalResidue A M r) N : ℝ) / N ≤ 1 :=
    (div_le_one hNr).mpr (by exact_mod_cast prefixCount_le (literalResidue A M r) N)
  simpa only [normalizedResiduePrefix, mul_one] using
    mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg (M : ℕ))

theorem isCompact_prefixProfileCompact (M : ℕ+) : IsCompact (prefixProfileCompact M) := by
  have hK : IsCompact (Set.pi Set.univ
      (fun _ : ZMod (M : ℕ) => Icc (0 : ℝ) ((M : ℕ) : ℝ))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact hK.prod hK

theorem residuePrefixPair_mem_compact (A B : Set ℕ) (M : ℕ+) (N : ℕ) :
    residuePrefixPair A B M N ∈ prefixProfileCompact M := by
  constructor
  · intro r hr
    exact normalized_residue_prefix_bound A M N r
  · intro r hr
    exact normalized_residue_prefix_bound B M N r

theorem exists_localProfile_extending_prefix_limits
    (A B : Set ℕ) (M : ℕ+) (a b : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (vA vB : ZMod (M : ℕ) → ℝ)
    (hLA : ∀ r, Tendsto (fun n => normalizedResiduePrefix A M (N n) r) atTop (𝓝 (vA r)))
    (hLB : ∀ r, Tendsto (fun n => normalizedResiduePrefix B M (N n) r) atTop (𝓝 (vB r))) :
    ∃ (σ : ℕ → ℕ)
      (p : LocalProfile (residues (M : ℕ) A) (residues (M : ℕ) B)
        (((M : ℕ) : ℝ) * a) (((M : ℕ) : ℝ) * b)),
      StrictMono σ ∧ p.left = vA ∧ p.right = vB ∧
      ∀ r, Tendsto (fun n => normalizedResiduePrefix (A + B) M (N (σ n)) r)
        atTop (𝓝 (p.output r)) := by
  let K : Set (ZMod (M : ℕ) → ℝ) :=
    Set.pi Set.univ (fun _ => Icc (0 : ℝ) ((M : ℕ) : ℝ))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem (n : ℕ) : normalizedResiduePrefix (A + B) M (N n) ∈ K :=
    fun r hr => normalized_residue_prefix_bound (A + B) M (N n) r
  obtain ⟨vC, _, σ, hσ, hlimit⟩ := hK.tendsto_subseq hmem
  have hLC (r : ZMod (M : ℕ)) : Tendsto
      (fun n => normalizedResiduePrefix (A + B) M (N (σ n)) r) atTop (𝓝 (vC r)) :=
    ((continuous_apply r).tendsto vC).comp hlimit
  have hLA' (r : ZMod (M : ℕ)) : Tendsto
      (fun n => normalizedResiduePrefix A M (N (σ n)) r) atTop (𝓝 (vA r)) :=
    (hLA r).comp hσ.tendsto_atTop
  have hLB' (r : ZMod (M : ℕ)) : Tendsto
      (fun n => normalizedResiduePrefix B M (N (σ n)) r) atTop (𝓝 (vB r)) :=
    (hLB r).comp hσ.tendsto_atTop
  obtain ⟨p, hpA, hpB, hpC⟩ := localProfile_of_residue_prefix_limits A B M a b hA hB hC
    (N ∘ σ) (hN.comp hσ.tendsto_atTop) vA vB vC hLA' hLB' hLC
  refine ⟨σ, p, hσ, hpA, hpB, ?_⟩
  intro r
  simpa only [hpC] using hLC r

theorem normalized_residue_prefix_step
    (A : Set ℕ) (M : ℕ+) (r : ZMod (M : ℕ)) :
    Tendsto (fun n => dist (normalizedResiduePrefix A M (n + 1) r)
      (normalizedResiduePrefix A M n r)) atTop (𝓝 0) :=
  normalized_prefix_step_tendsto_zero (literalResidue A M r) ((M : ℕ) : ℝ)
    (Nat.cast_nonneg _)

theorem normalized_residue_vector_step
    (A : Set ℕ) (M : ℕ+) :
    Tendsto (fun n => normalizedResiduePrefix A M (n + 1) - normalizedResiduePrefix A M n)
      atTop (𝓝 (0 : ZMod (M : ℕ) → ℝ)) := by
  apply tendsto_pi_nhds.mpr
  intro r
  change Tendsto (fun n => normalizedResiduePrefix A M (n + 1) r -
    normalizedResiduePrefix A M n r) atTop (𝓝 0)
  apply (tendsto_zero_iff_norm_tendsto_zero).mpr
  simpa only [dist_eq_norm] using normalized_residue_prefix_step A M r

theorem residuePrefixPair_step (A B : Set ℕ) (M : ℕ+) :
    Tendsto (fun n => dist (residuePrefixPair A B M (n + 1))
      (residuePrefixPair A B M n)) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun n => residuePrefixPair A B M (n + 1) - residuePrefixPair A B M n)
      atTop (𝓝 (0 : (ZMod (M : ℕ) → ℝ) × (ZMod (M : ℕ) → ℝ))) := by
    exact (normalized_residue_vector_step A M).prodMk_nhds (normalized_residue_vector_step B M)
  simpa only [dist_eq_norm, norm_zero] using hdiff.norm

theorem prefix_pair_cluster_localProfile
    (A B : Set ℕ) (M : ℕ+) (a b : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (v : (ZMod (M : ℕ) → ℝ) × (ZMod (M : ℕ) → ℝ))
    (hv : MapClusterPt v atTop (residuePrefixPair A B M)) :
    ∃ p : LocalProfile (residues (M : ℕ) A) (residues (M : ℕ) B)
        (((M : ℕ) : ℝ) * a) (((M : ℕ) : ℝ) * b),
      p.left = v.1 ∧ p.right = v.2 := by
  obtain ⟨σ, hσ, hlimit⟩ := hv.tendsto_subseq
  have hLA (r : ZMod (M : ℕ)) : Tendsto
      (fun n => normalizedResiduePrefix A M (σ n) r) atTop (𝓝 (v.1 r)) :=
    (((continuous_apply r).comp continuous_fst).tendsto v).comp hlimit
  have hLB (r : ZMod (M : ℕ)) : Tendsto
      (fun n => normalizedResiduePrefix B M (σ n) r) atTop (𝓝 (v.2 r)) :=
    (((continuous_apply r).comp continuous_snd).tendsto v).comp hlimit
  obtain ⟨_, p, _, hpA, hpB, _⟩ := exists_localProfile_extending_prefix_limits A B M a b
    hA hB hC σ hσ.tendsto_atTop v.1 v.2 hLA hLB
  exact ⟨p, hpA, hpB⟩

end Erdos335.PeriodicRefinement

end
