import Erdos335.PeriodicRefinementCumulative
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Sequences

/-!
# Compactness of the cumulative-count profiles

The compact-open topology retains convergence on every bounded interval of the
positive half-line, including all integer enlargements of the macroscopic scale.
-/

set_option autoImplicit false

open Filter Set Topology

noncomputable section

namespace Erdos335.PeriodicRefinement

def cumulativeProfileSpace : Set C(ℝ, ℝ) :=
  {f | LipschitzWith 1 f ∧ f 0 = 0}

theorem cumulativeProfileSpace_compact : IsCompact cumulativeProfileSpace := by
  let K : Set (ℝ → ℝ) := {f | LipschitzWith 1 f ∧ f 0 = 0}
  have hclosed : IsClosed K :=
    (isClosed_setOfPred_lipschitzWith 1).inter
      (isClosed_eq (continuous_apply 0) continuous_const)
  have hbound : K ⊆ Set.pi Set.univ (fun x : ℝ => Set.Icc (-|x|) |x|) := by
    intro f hf x _
    have hb := hf.1.dist_le_mul x 0
    rw [hf.2] at hb
    simpa only [NNReal.coe_one, one_mul, dist_zero_right, Real.norm_eq_abs,
      abs_le, Set.mem_Icc] using hb
  have hcompact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hbound
  have himage : ContinuousMap.toFun '' cumulativeProfileSpace = K := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hf.1.continuous⟩, hf, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rwa [himage]
  · apply Metric.equicontinuous_of_continuity_modulus (fun x : ℝ => x)
      (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0))
    intro x y f
    simpa only [NNReal.coe_one, one_mul] using f.2.1.dist_le_mul x y

theorem exists_cumulative_profile_subsequence
    {ι : Type*} [Fintype ι] (f : ℕ → ι → C(ℝ, ℝ))
    (hf : ∀ n i, LipschitzWith 1 (f n i) ∧ f n i 0 = 0) :
    ∃ (σ : ℕ → ℕ) (F : ι → C(ℝ, ℝ)), StrictMono σ ∧
      (∀ i, LipschitzWith 1 (F i) ∧ F i 0 = 0) ∧
      Tendsto (f ∘ σ) atTop (𝓝 F) := by
  have hcompact : IsCompact (Set.pi Set.univ (fun _ : ι => cumulativeProfileSpace)) :=
    isCompact_univ_pi fun _ => cumulativeProfileSpace_compact
  obtain ⟨F, hF, σ, hσ, hlim⟩ := hcompact.tendsto_subseq (fun n i _ => hf n i)
  exact ⟨σ, F, hσ, fun i => hF i (Set.mem_univ i), hlim⟩

theorem exists_joint_cumulative_limits
    {ι : Type*} [Fintype ι] (S : ι → Set ℕ)
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∃ (σ : ℕ → ℕ) (G : ι → ℝ → ℝ) (F : ι → C(ℝ, ℝ)),
      StrictMono σ ∧
      (∀ i, LipschitzWith 1 (G i) ∧ (∀ k : ℕ, G i k = prefixCount (S i) k)) ∧
      (∀ i, LipschitzWith 1 (F i) ∧ F i 0 = 0) ∧
      (∀ i (K : Set ℝ), IsCompact K →
        TendstoUniformlyOn (fun n t => G i (t * N (σ n)) / N (σ n)) (F i) atTop K) ∧
      (∀ n i t, 0 ≤ t →
        |G i (t * N (σ n)) / N (σ n) -
          (prefixCount (S i) (Nat.floor (t * N (σ n))) : ℝ) / N (σ n)|
            ≤ 1 / N (σ n)) := by
  classical
  choose G hG hgrid hzero using fun i => exists_continuous_prefix_count (S i)
  let f : ℕ → ι → C(ℝ, ℝ) := fun n i =>
    ⟨fun t => G i (t * N n) / N n,
      (rescaled_prefix_count_lipschitz (G i) (hG i) (N n) (hN n)).continuous⟩
  have hf : ∀ n i, LipschitzWith 1 (f n i) ∧ f n i 0 = 0 := by
    intro n i
    refine ⟨rescaled_prefix_count_lipschitz (G i) (hG i) (N n) (hN n), ?_⟩
    simp [f, hzero]
  obtain ⟨σ, F, hσ, hF, hlim⟩ := exists_cumulative_profile_subsequence f hf
  refine ⟨σ, G, F, hσ, fun i => ⟨hG i, hgrid i⟩, hF, ?_, ?_⟩
  · intro i K hK
    have hi := (tendsto_pi_nhds.mp hlim) i
    exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hi) K hK
  · intro n i t ht
    exact rescaled_prefix_count_error (S i) (G i) (hG i) (hgrid i)
      (N (σ n)) (hN (σ n)) t ht

end Erdos335.PeriodicRefinement

end
