import Erdos335.MaskDensity
import Erdos335.DensityLimits

/-!
# Common asymptotic periods and sparse mask transitions

The equivalence uses literal membership in every residue, including the
initial block. Fixed endpoint effects are controlled by density-zero sets.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem blockSet_mask_eq (A : Set ℕ) (q : ℕ+) : blockSet q (mask A q) = A := by
  ext n
  change (n : ZMod (q : ℕ)) ∈ mask A q (n / (q : ℕ)) ↔ n ∈ A
  rw [mem_mask]
  have hn : (q : ℕ) * (n / (q : ℕ)) + (n : ZMod (q : ℕ)).val = n := by
    simpa only [ZMod.val_natCast, Nat.add_comm] using Nat.mod_add_div n (q : ℕ)
  rw [hn]

theorem shift_equivalent_of_sparse_mask (A : Set ℕ) (q : ℕ+)
    (hsparse : Negligible (transitionIndices (mask A q))) :
    DensityEquivalent (shift A (q : ℕ)) A := by
  have h := translated_mask_equiv A q (q : ℕ) hsparse
  have hbase : blockSet q (fun k => mask A q k + {((q : ℕ) : ZMod (q : ℕ))}) =
      blockSet q (mask A q) := by
    ext n
    change (n : ZMod (q : ℕ)) ∈ mask A q (n / (q : ℕ)) +
      {((q : ℕ) : ZMod (q : ℕ))} ↔ (n : ZMod (q : ℕ)) ∈ mask A q (n / (q : ℕ))
    rw [ZMod.natCast_self]
    constructor
    · intro hn
      obtain ⟨r, hr, t, ht, hrt⟩ := Finset.mem_add.mp hn
      have ht0 : t = 0 := Finset.mem_singleton.mp ht
      have hrn : r = (n : ZMod (q : ℕ)) := by simpa only [ht0, add_zero] using hrt
      exact hrn ▸ hr
    · intro hn
      exact Finset.mem_add.mpr ⟨_, hn, 0, by simp, by simp⟩
  rwa [hbase, blockSet_mask_eq A q] at h

theorem sparse_mask_of_shift_equivalent (A : Set ℕ) (q : ℕ+)
    (h : DensityEquivalent (shift A (q : ℕ)) A) :
    Negligible (transitionIndices (mask A q)) := by
  classical
  let D := (shift A (q : ℕ) \ A) ∪ (A \ shift A (q : ℕ))
  have hD : Negligible D := h.1.union h.2
  let E := fun r : ZMod (q : ℕ) => {k : ℕ | (q : ℕ) * (k + 1) + r.val ∈ D}
  have hE : ∀ r : ZMod (q : ℕ), Negligible (E r) := by
    intro r
    have hr := (hD.arithmetic_preimage q r.val_lt).tailShift 1
    simpa [Negligible, tailShift, E] using hr
  apply (negligible_finiteUnion Finset.univ E (fun r _ => hE r)).mono
  intro k hk
  have hex : ∃ r : ZMod (q : ℕ), ¬(r ∈ mask A q k ↔ r ∈ mask A q (k + 1)) := by
    by_contra hnone
    push Not at hnone
    apply hk
    exact Finset.ext hnone
  obtain ⟨r, hne⟩ := hex
  have hshift : (q : ℕ) * (k + 1) + r.val ∈ shift A (q : ℕ) ↔
      (q : ℕ) * k + r.val ∈ A := by
    constructor
    · rintro ⟨a, ha, heq⟩
      have heq' : a = (q : ℕ) * k + r.val := by
        change a + (q : ℕ) = (q : ℕ) * (k + 1) + r.val at heq
        nlinarith
      exact heq' ▸ ha
    · intro ha
      exact ⟨(q : ℕ) * k + r.val, ha, by dsimp only; ring⟩
  rw [mem_mask, mem_mask] at hne
  refine ⟨r, Finset.mem_univ _, ?_⟩
  change (q : ℕ) * (k + 1) + r.val ∈ D
  by_cases hnow : (q : ℕ) * k + r.val ∈ A
  · left
    exact ⟨hshift.mpr hnow, fun hnext => hne (iff_of_true hnow hnext)⟩
  · right
    refine ⟨?_, fun hprev => hnow (hshift.mp hprev)⟩
    by_contra hnext
    exact hne (iff_of_false hnow hnext)

theorem sparseTransitions_iff_shift_equivalent (A B : Set ℕ) (q : ℕ+) :
    SparseTransitions A B q ↔
      DensityEquivalent (shift A (q : ℕ)) A ∧ DensityEquivalent (shift B (q : ℕ)) B := by
  constructor
  · intro h
    exact ⟨shift_equivalent_of_sparse_mask A q h.maskA,
      shift_equivalent_of_sparse_mask B q h.maskB⟩
  · rintro ⟨hA, hB⟩
    apply (sparseTransitions_iff A B q).mpr
    apply ((sparse_mask_of_shift_equivalent A q hA).union
      (sparse_mask_of_shift_equivalent B q hB)).mono
    intro k hk
    by_cases hleft : mask A q k = mask A q (k + 1)
    · right
      intro hright
      exact hk (Prod.ext hleft hright)
    · exact Or.inl hleft

end Erdos335.Proposed
