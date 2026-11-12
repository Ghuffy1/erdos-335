import Erdos335.MaskDensity
import Erdos335.PackedIntervals
import Erdos335.ShiftTransitions

/-!
# Finite-translate coverage and the exact mask branch

For inputs with sparse block-mask transitions, finite literal translates
describe the same-time output masks in density. This identifies the remaining
coverage statement needed to obtain the mask branch in the necessity proof.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem DensityEquivalent.union {A B C D : Set ℕ}
    (hAB : DensityEquivalent A B) (hCD : DensityEquivalent C D) :
    DensityEquivalent (A ∪ C) (B ∪ D) := by
  constructor
  · apply (hAB.1.union hCD.1).mono
    rintro n ⟨hn | hn, hout⟩
    · exact Or.inl ⟨hn, fun h => hout (Or.inl h)⟩
    · exact Or.inr ⟨hn, fun h => hout (Or.inr h)⟩
  · apply (hAB.2.union hCD.2).mono
    rintro n ⟨hn | hn, hout⟩
    · exact Or.inl ⟨hn, fun h => hout (Or.inl h)⟩
    · exact Or.inr ⟨hn, fun h => hout (Or.inr h)⟩

namespace Proposed

def finiteTranslateCover (A B : Set ℕ) (FA FB : Finset ℕ) : Set ℕ :=
  finiteUnion FB (shift A) ∪ finiteUnion FA (shift B)

theorem finite_shifts_outside_left_mask_negligible (A B : Set ℕ) (q : ℕ+)
    (F : Finset ℕ) (hF : (F : Set ℕ) ⊆ B)
    (hsparse : Negligible (transitionIndices (mask A q))) :
    Negligible (finiteUnion F (shift A) \
      blockSet q (fun k => mask A q k + residues (q : ℕ) B)) := by
  have hbad : ∀ b ∈ F, Negligible (shift A b \
      blockSet q (fun k => mask A q k + residues (q : ℕ) B)) := by
    intro b hb
    apply (translated_mask_equiv A q b hsparse).1.mono
    rintro n ⟨hn, hout⟩
    refine ⟨hn, ?_⟩
    intro hm
    apply hout
    exact Finset.add_subset_add (Finset.Subset.refl _)
      (Finset.singleton_subset_iff.mpr (mem_residues.mpr ⟨b, hF hb, rfl⟩)) hm
  apply (negligible_finiteUnion F _ hbad).mono
  rintro n ⟨⟨b, hb, hn⟩, hout⟩
  exact ⟨b, hb, hn, hout⟩

theorem left_mask_missing_finite_shifts_negligible (A B : Set ℕ) (q : ℕ+)
    (F : Finset ℕ)
    (hrep : ∀ r ∈ residues (q : ℕ) B, ∃ b ∈ F, (b : ZMod (q : ℕ)) = r)
    (hsparse : Negligible (transitionIndices (mask A q))) :
    Negligible (blockSet q (fun k => mask A q k + residues (q : ℕ) B) \
      finiteUnion F (shift A)) := by
  classical
  let E := fun r : ZMod (q : ℕ) =>
    blockSet q (fun k => mask A q k + {r}) \ finiteUnion F (shift A)
  have hE : ∀ r ∈ residues (q : ℕ) B, Negligible (E r) := by
    intro r hr
    obtain ⟨b, hb, hbr⟩ := hrep r hr
    apply (translated_mask_equiv A q b hsparse).2.mono
    rintro n ⟨hn, hout⟩
    refine ⟨by simpa only [hbr] using hn, ?_⟩
    intro hshift
    exact hout ⟨b, hb, hshift⟩
  apply (negligible_finiteUnion (residues (q : ℕ) B) E hE).mono
  rintro n ⟨hn, hout⟩
  obtain ⟨r, hr, t, ht, hrt⟩ := Finset.mem_add.mp hn
  exact ⟨t, ht, Finset.mem_add.mpr ⟨r, hr, t, Finset.mem_singleton_self _, hrt⟩, hout⟩

theorem finite_shifts_equiv_left_mask (A B : Set ℕ) (q : ℕ+)
    (F : Finset ℕ) (hF : (F : Set ℕ) ⊆ B)
    (hrep : ∀ r ∈ residues (q : ℕ) B, ∃ b ∈ F, (b : ZMod (q : ℕ)) = r)
    (hsparse : Negligible (transitionIndices (mask A q))) :
    DensityEquivalent (finiteUnion F (shift A))
      (blockSet q (fun k => mask A q k + residues (q : ℕ) B)) :=
  ⟨finite_shifts_outside_left_mask_negligible A B q F hF hsparse,
    left_mask_missing_finite_shifts_negligible A B q F hrep hsparse⟩

theorem output_mask_decomposition (A B : Set ℕ) (q : ℕ+) :
    blockSet q (outputMask A B q) =
      blockSet q (fun k => mask A q k + residues (q : ℕ) B) ∪
      blockSet q (fun k => mask B q k + residues (q : ℕ) A) := by
  ext n
  change (n : ZMod (q : ℕ)) ∈
      (mask A q (n / (q : ℕ)) + residues (q : ℕ) B) ∪
        (residues (q : ℕ) A + mask B q (n / (q : ℕ))) ↔ _
  rw [add_comm (residues (q : ℕ) A)]
  simp only [Finset.mem_union, Set.mem_union, blockSet, Set.mem_ofPred_eq]

theorem finite_translate_cover_equiv_output_mask (A B : Set ℕ) (q : ℕ+)
    (FA FB : Finset ℕ) (hFA : (FA : Set ℕ) ⊆ A) (hFB : (FB : Set ℕ) ⊆ B)
    (hrepA : ∀ r ∈ residues (q : ℕ) A, ∃ a ∈ FA, (a : ZMod (q : ℕ)) = r)
    (hrepB : ∀ r ∈ residues (q : ℕ) B, ∃ b ∈ FB, (b : ZMod (q : ℕ)) = r)
    (hsparse : SparseTransitions A B q) :
    DensityEquivalent (finiteTranslateCover A B FA FB) (blockSet q (outputMask A B q)) := by
  rw [output_mask_decomposition]
  exact (finite_shifts_equiv_left_mask A B q FB hFB hrepB hsparse.maskA).union
    (finite_shifts_equiv_left_mask B A q FA hFA hrepA hsparse.maskB)

theorem finite_translate_cover_outside_output_negligible (A B : Set ℕ) (q : ℕ+)
    (FA FB : Finset ℕ) (hFA : (FA : Set ℕ) ⊆ A) (hFB : (FB : Set ℕ) ⊆ B)
    (hsparse : SparseTransitions A B q) :
    Negligible (finiteTranslateCover A B FA FB \ blockSet q (outputMask A B q)) := by
  rw [output_mask_decomposition]
  have hleft := finite_shifts_outside_left_mask_negligible A B q FB hFB hsparse.maskA
  have hright := finite_shifts_outside_left_mask_negligible B A q FA hFA hsparse.maskB
  apply (hleft.union hright).mono
  rintro n ⟨hn | hn, hout⟩
  · exact Or.inl ⟨hn, fun h => hout (Or.inl h)⟩
  · exact Or.inr ⟨hn, fun h => hout (Or.inr h)⟩

theorem maskBranch_of_finite_translate_cover (A B : Set ℕ) (q : ℕ+) (s : ℝ)
    (hsparse : SparseTransitions A B q) (hC : HasDensity (A + B) s)
    (FA FB : Finset ℕ) (hFA : (FA : Set ℕ) ⊆ A) (hFB : (FB : Set ℕ) ⊆ B)
    (hcover : Negligible ((A + B) \ finiteTranslateCover A B FA FB)) :
    MaskBranch A B s := by
  have hsmall := finite_translate_cover_outside_output_negligible A B q FA FB hFA hFB hsparse
  have hout : Negligible ((A + B) \ blockSet q (outputMask A B q)) := by
    apply (hcover.union hsmall).mono
    rintro n ⟨hn, hnout⟩
    by_cases hmem : n ∈ finiteTranslateCover A B FA FB
    · exact Or.inr ⟨hmem, hnout⟩
    · exact Or.inl ⟨hn, hmem⟩
  have heq : DensityEquivalent (A + B) (blockSet q (outputMask A B q)) :=
    ⟨hout, missing_output_negligible A B q hsparse⟩
  exact ⟨q, hsparse, (hasDensity_blockSet_iff q (outputMask A B q) s).mp (heq.hasDensity hC),
    (escapingPackingVanishes_iff_negligible A B q).mpr hout⟩

theorem MaskBranch.finite_translate_cover {A B : Set ℕ} {s : ℝ}
    (h : MaskBranch A B s) :
    ∃ (q : ℕ+) (FA FB : Finset ℕ), SparseTransitions A B q ∧
      (FA : Set ℕ) ⊆ A ∧ (FB : Set ℕ) ⊆ B ∧
        Negligible ((A + B) \ finiteTranslateCover A B FA FB) := by
  obtain ⟨q, hsparse, hmean, hpacking⟩ := h
  obtain ⟨FA, hFA, hrepA⟩ := exists_finite_residue_representatives A q
  obtain ⟨FB, hFB, hrepB⟩ := exists_finite_residue_representatives B q
  have heq := finite_translate_cover_equiv_output_mask A B q FA FB hFA hFB hrepA hrepB hsparse
  have hout := escaping_negligible_of_packing A B q hpacking
  refine ⟨q, FA, FB, hsparse, hFA, hFB, ?_⟩
  apply (hout.union heq.2).mono
  rintro n ⟨hn, hnout⟩
  by_cases hmem : n ∈ blockSet q (outputMask A B q)
  · exact Or.inr ⟨hmem, hnout⟩
  · exact Or.inl ⟨hn, hmem⟩

theorem maskBranch_iff_sparse_density_finite_translate_cover (A B : Set ℕ) (s : ℝ) :
    MaskBranch A B s ↔ HasDensity (A + B) s ∧
      ∃ (q : ℕ+) (FA FB : Finset ℕ), SparseTransitions A B q ∧
        (FA : Set ℕ) ⊆ A ∧ (FB : Set ℕ) ⊆ B ∧
          Negligible ((A + B) \ finiteTranslateCover A B FA FB) := by
  constructor
  · intro h
    exact ⟨maskBranch_hasDensity A B s h, h.finite_translate_cover⟩
  · rintro ⟨hC, q, FA, FB, hsparse, hFA, hFB, hcover⟩
    exact maskBranch_of_finite_translate_cover A B q s hsparse hC FA FB hFA hFB hcover

theorem maskBranch_iff_common_period_finite_translate_cover (A B : Set ℕ) (s : ℝ) :
    MaskBranch A B s ↔ HasDensity (A + B) s ∧
      ∃ (q : ℕ+) (FA FB : Finset ℕ),
        DensityEquivalent (shift A (q : ℕ)) A ∧ DensityEquivalent (shift B (q : ℕ)) B ∧
          (FA : Set ℕ) ⊆ A ∧ (FB : Set ℕ) ⊆ B ∧
            Negligible ((A + B) \ finiteTranslateCover A B FA FB) := by
  rw [maskBranch_iff_sparse_density_finite_translate_cover]
  constructor
  · rintro ⟨hC, q, FA, FB, hsparse, hFA, hFB, hcover⟩
    obtain ⟨hA, hB⟩ := (sparseTransitions_iff_shift_equivalent A B q).mp hsparse
    exact ⟨hC, q, FA, FB, hA, hB, hFA, hFB, hcover⟩
  · rintro ⟨hC, q, FA, FB, hA, hB, hFA, hFB, hcover⟩
    exact ⟨hC, q, FA, FB, (sparseTransitions_iff_shift_equivalent A B q).mpr ⟨hA, hB⟩,
      hFA, hFB, hcover⟩

end Proposed
end Erdos335
