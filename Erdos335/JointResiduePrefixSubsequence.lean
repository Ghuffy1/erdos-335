import Erdos335.BlockCounting
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Joint compact extraction of two finite residue-prefix vectors

Private proof development. Verification status is recorded separately. Every coordinate is bounded by the fixed
modulus. Compact extraction applies to both sets and all residues together.
-/

set_option autoImplicit false

open Filter Set Topology

noncomputable section

namespace Erdos335

theorem exists_joint_residue_prefix_subsequence
    (A B : Set ℕ) (M : ℕ+) (H : ℕ → ℕ) (hH : ∀ s, 0 < H s) :
    ∃ (σ : ℕ → ℕ) (vA vB : ZMod (M : ℕ) → ℝ),
      StrictMono σ ∧
      (∀ r, vA r ∈ Set.Icc (0 : ℝ) ((M : ℕ) : ℝ)) ∧
      (∀ r, vB r ∈ Set.Icc (0 : ℝ) ((M : ℕ) : ℝ)) ∧
      (∀ r, Tendsto (fun s => ((M : ℕ) : ℝ) *
        ((prefixCount {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r} (H (σ s)) : ℝ) /
          H (σ s))) atTop (𝓝 (vA r))) ∧
      (∀ r, Tendsto (fun s => ((M : ℕ) : ℝ) *
        ((prefixCount {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r} (H (σ s)) : ℝ) /
          H (σ s))) atTop (𝓝 (vB r))) := by
  classical
  let u : ℕ → (Bool × ZMod (M : ℕ) → ℝ) := fun s t => ((M : ℕ) : ℝ) *
    ((prefixCount {k : ℕ | k ∈ (if t.1 then B else A) ∧
      (k : ZMod (M : ℕ)) = t.2} (H s) : ℝ) / H s)
  have hu (s : ℕ) (t : Bool × ZMod (M : ℕ)) :
      u s t ∈ Set.Icc (0 : ℝ) ((M : ℕ) : ℝ) := by
    have hHr : (0 : ℝ) < H s := by exact_mod_cast hH s
    have hcount : prefixCount {k : ℕ | k ∈ (if t.1 then B else A) ∧
        (k : ZMod (M : ℕ)) = t.2} (H s) ≤ H s := by
      simpa only [prefixCount, Set.mem_setOf_eq, Finset.card_range] using
        Finset.card_le_card (Finset.filter_subset
          (fun k : ℕ => k ∈ (if t.1 then B else A) ∧ (k : ZMod (M : ℕ)) = t.2)
          (Finset.range (H s)))
    have hratio : (prefixCount {k : ℕ | k ∈ (if t.1 then B else A) ∧
        (k : ZMod (M : ℕ)) = t.2} (H s) : ℝ) / H s ≤ 1 := by
      apply (div_le_iff₀ hHr).mpr
      simpa only [one_mul] using (show
        (prefixCount {k : ℕ | k ∈ (if t.1 then B else A) ∧
          (k : ZMod (M : ℕ)) = t.2} (H s) : ℝ) ≤ H s by exact_mod_cast hcount)
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) hHr.le), ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio
      (show (0 : ℝ) ≤ ((M : ℕ) : ℝ) by positivity)
  let K : Set (Bool × ZMod (M : ℕ) → ℝ) :=
    Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) ((M : ℕ) : ℝ))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨v, hv, σ, hσ, hlimit⟩ := hK.tendsto_subseq (fun s t _ => hu s t)
  refine ⟨σ, (fun r => v (false, r)), (fun r => v (true, r)), hσ, ?_, ?_, ?_, ?_⟩
  · intro r
    exact hv (false, r) (Set.mem_univ _)
  · intro r
    exact hv (true, r) (Set.mem_univ _)
  · intro r
    simpa [u, Function.comp_def] using (tendsto_pi_nhds.mp hlimit) (false, r)
  · intro r
    simpa [u, Function.comp_def] using (tendsto_pi_nhds.mp hlimit) (true, r)

end Erdos335

end
