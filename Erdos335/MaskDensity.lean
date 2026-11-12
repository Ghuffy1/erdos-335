import Erdos335.BlockCounting
import Erdos335.RunIntervals

/-!
# Density of the literal output masks

Sparse changes of the exact paired masks control each fixed literal translate.
The interval condition controls all remaining representations.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem sparseTransitions_iff (A B : Set ℕ) (q : ℕ+) :
    SparseTransitions A B q ↔ Negligible (transitionIndices (pairedMask A B q)) := by
  classical
  change SparseTransitions A B q ↔ HasDensity (transitionIndices (pairedMask A B q)) 0
  rw [hasDensity_iff_prefixCount]
  have hcount : ∀ N, prefixCount (transitionIndices (pairedMask A B q)) N =
      transitionCount A B q N := by
    intro N
    unfold prefixCount transitionCount
    congr 1
    apply Finset.filter_congr
    intro k hk
    rfl
  simp only [hcount, SparseTransitions]

theorem SparseTransitions.maskA {A B : Set ℕ} {q : ℕ+}
    (h : SparseTransitions A B q) : Negligible (transitionIndices (mask A q)) := by
  apply ((sparseTransitions_iff A B q).mp h).mono
  intro k hk heq
  exact hk (congrArg Prod.fst heq)

theorem SparseTransitions.maskB {A B : Set ℕ} {q : ℕ+}
    (h : SparseTransitions A B q) : Negligible (transitionIndices (mask B q)) := by
  apply ((sparseTransitions_iff A B q).mp h).mono
  intro k hk heq
  exact hk (congrArg Prod.snd heq)

theorem mem_shift_iff_mask (A : Set ℕ) (q : ℕ+) (b n : ℕ) (hb : b ≤ n) :
    n ∈ shift A b ↔ (n : ZMod (q : ℕ)) ∈
      mask A q ((n - b) / (q : ℕ)) + {(b : ZMod (q : ℕ))} := by
  classical
  have hdecomp : (q : ℕ) * ((n - b) / (q : ℕ)) +
      ((n - b : ℕ) : ZMod (q : ℕ)).val = n - b := by
    simpa only [ZMod.val_natCast, Nat.add_comm] using Nat.mod_add_div (n - b) (q : ℕ)
  have hsum : ((n - b : ℕ) : ZMod (q : ℕ)) + (b : ZMod (q : ℕ)) = n := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hb]
  constructor
  · rintro ⟨a, ha, hna⟩
    change a + b = n at hna
    have ha' : n - b ∈ A := by
      have heq : n - b = a := by omega
      simpa only [heq] using ha
    have hmask : ((n - b : ℕ) : ZMod (q : ℕ)) ∈
        mask A q ((n - b) / (q : ℕ)) := by
      apply mem_mask.mpr
      simpa only [hdecomp] using ha'
    exact Finset.mem_add.mpr ⟨_, hmask, _, Finset.mem_singleton_self _, hsum⟩
  · intro hn
    obtain ⟨r, hr, t, ht, hrt⟩ := Finset.mem_add.mp hn
    have ht' : t = (b : ZMod (q : ℕ)) := Finset.mem_singleton.mp ht
    subst t
    have hr' : r = ((n - b : ℕ) : ZMod (q : ℕ)) := add_right_cancel (hrt.trans hsum.symm)
    rw [hr'] at hr
    have ha := mem_mask.mp hr
    rw [hdecomp] at ha
    exact ⟨n - b, ha, Nat.sub_add_cancel hb⟩

theorem block_lag_bound (q : ℕ+) {b n : ℕ} (hb : b ≤ n) :
    (n - b) / (q : ℕ) ≤ n / (q : ℕ) ∧
      n / (q : ℕ) - (n - b) / (q : ℕ) ≤ b := by
  have hlo : (n - b) / (q : ℕ) ≤ n / (q : ℕ) := Nat.div_le_div_right (Nat.sub_le n b)
  have hrem := Nat.mod_lt (n - b) q.pos
  have hdiv := Nat.mod_add_div (n - b) (q : ℕ)
  have hbmul := Nat.le_mul_of_pos_left b q.pos
  have hupper : n / (q : ℕ) < (n - b) / (q : ℕ) + b + 1 := by
    apply (Nat.div_lt_iff_lt_mul q.pos).mpr
    have hsub : n - b + b = n := Nat.sub_add_cancel hb
    nlinarith
  exact ⟨hlo, by omega⟩

theorem translated_mask_equiv (A : Set ℕ) (q : ℕ+) (b : ℕ)
    (h : Negligible (transitionIndices (mask A q))) :
    DensityEquivalent (shift A b)
      (blockSet q (fun k => mask A q k + {(b : ZMod (q : ℕ))})) := by
  classical
  let bad := finiteUnion (Finset.range (b + 1)) (fun d => {k | mask A q (k - d) ≠ mask A q k})
  have hbad : Negligible bad := negligible_finiteUnion _ _
    (fun d _ => h.backward_difference d)
  have hsmall : Negligible {n : ℕ | n < b} :=
    Negligible.of_bounded b (by intro n hn; exact Nat.le_of_lt hn)
  have hzero := (hbad.liftBlocks q).union hsmall
  have hgood : ∀ n, b ≤ n → n ∉ liftBlocks q bad →
      (n ∈ shift A b ↔ n ∈ blockSet q (fun k => mask A q k + {(b : ZMod (q : ℕ))})) := by
    intro n hb hn
    have hlag := block_lag_bound q hb
    have heq : mask A q ((n - b) / (q : ℕ)) = mask A q (n / (q : ℕ)) := by
      by_contra hne
      apply hn
      change ∃ d ∈ Finset.range (b + 1),
        mask A q (n / (q : ℕ) - d) ≠ mask A q (n / (q : ℕ))
      refine ⟨n / (q : ℕ) - (n - b) / (q : ℕ), Finset.mem_range.mpr (by omega), ?_⟩
      simpa only [Nat.sub_sub_self hlag.1] using hne
    rw [mem_shift_iff_mask A q b n hb, heq]
    rfl
  constructor
  · apply hzero.mono
    rintro n ⟨hn, hout⟩
    by_cases hb : b ≤ n
    · by_cases hbadn : n ∈ liftBlocks q bad
      · exact Or.inl hbadn
      · exact (hout ((hgood n hb hbadn).mp hn)).elim
    · exact Or.inr (show n < b from Nat.lt_of_not_ge hb)
  · apply hzero.mono
    rintro n ⟨hn, hout⟩
    by_cases hb : b ≤ n
    · by_cases hbadn : n ∈ liftBlocks q bad
      · exact Or.inl hbadn
      · exact (hout ((hgood n hb hbadn).mpr hn)).elim
    · exact Or.inr (show n < b from Nat.lt_of_not_ge hb)

theorem missing_left_output_negligible (A B : Set ℕ) (q : ℕ+)
    (h : Negligible (transitionIndices (mask A q))) :
    Negligible (blockSet q (fun k => mask A q k + residues (q : ℕ) B) \ (A + B)) := by
  classical
  let D := fun t : ZMod (q : ℕ) =>
    blockSet q (fun k => mask A q k + {t}) \ (A + B)
  have hD : ∀ t ∈ residues (q : ℕ) B, Negligible (D t) := by
    intro t ht
    obtain ⟨b, hb, hbt⟩ := mem_residues.mp ht
    have heq := translated_mask_equiv A q b h
    apply heq.2.mono
    rintro n ⟨hn, hout⟩
    refine ⟨?_, ?_⟩
    · simpa only [hbt] using hn
    · intro hnshift
      apply hout
      simpa only [add_comm] using shift_subset_sum hb hnshift
  apply (negligible_finiteUnion (residues (q : ℕ) B) D hD).mono
  rintro n ⟨hn, hout⟩
  obtain ⟨r, hr, t, ht, hrt⟩ := Finset.mem_add.mp hn
  refine ⟨t, ht, ?_, hout⟩
  exact Finset.mem_add.mpr ⟨r, hr, t, Finset.mem_singleton_self t, hrt⟩

theorem missing_output_negligible (A B : Set ℕ) (q : ℕ+)
    (h : SparseTransitions A B q) :
    Negligible (blockSet q (outputMask A B q) \ (A + B)) := by
  have hleft := missing_left_output_negligible A B q h.maskA
  have hright := missing_left_output_negligible B A q h.maskB
  apply (hleft.union hright).mono
  rintro n ⟨hn, hout⟩
  change (n : ZMod (q : ℕ)) ∈
    (mask A q (n / (q : ℕ)) + residues (q : ℕ) B) ∪
      (residues (q : ℕ) A + mask B q (n / (q : ℕ))) at hn
  rcases Finset.mem_union.mp hn with hL | hR
  · exact Or.inl ⟨hL, hout⟩
  · right
    refine ⟨?_, ?_⟩
    · change (n : ZMod (q : ℕ)) ∈ mask B q (n / (q : ℕ)) + residues (q : ℕ) A
      simpa only [add_comm] using hR
    · simpa only [add_comm] using hout

theorem escaping_negligible_of_packing (A B : Set ℕ) (q : ℕ+)
    (h : EscapingPackingVanishes A B q) :
    Negligible ((A + B) \ blockSet q (outputMask A B q)) := by
  classical
  let D := fun w : ZMod (q : ℕ) =>
    {k | (q : ℕ) * k + w.val ∈ A + B ∧ w ∉ outputMask A B q k}
  have hD : ∀ w, Negligible (D w) := by
    intro w
    apply (hasDensity_iff_prefixCount (D w) 0).mpr
    have hw := (escapingPackingVanishes_iff A B q).mp h w
    simpa only [escapingIndices, prefixCount, D, Set.mem_ofPred_eq] using hw
  have hfinite := negligible_finiteUnion Finset.univ D (fun w _ => hD w)
  apply (hfinite.liftBlocks q).mono
  rintro n ⟨hn, hout⟩
  change ∃ w ∈ (Finset.univ : Finset (ZMod (q : ℕ))), n / (q : ℕ) ∈ D w
  refine ⟨(n : ZMod (q : ℕ)), Finset.mem_univ _, ?_, hout⟩
  have hdecomp : (q : ℕ) * (n / (q : ℕ)) + (n : ZMod (q : ℕ)).val = n := by
    simpa only [ZMod.val_natCast, Nat.add_comm] using Nat.mod_add_div n (q : ℕ)
  simpa only [hdecomp] using hn

theorem escapingPackingVanishes_iff_negligible (A B : Set ℕ) (q : ℕ+) :
    EscapingPackingVanishes A B q ↔
      Negligible ((A + B) \ blockSet q (outputMask A B q)) := by
  classical
  constructor
  · exact escaping_negligible_of_packing A B q
  · intro h
    apply (escapingPackingVanishes_iff A B q).mpr
    intro w
    let D : Set ℕ := {k | (q : ℕ) * k + w.val ∈ A + B ∧ w ∉ outputMask A B q k}
    have hD : Negligible D := by
      apply (h.arithmetic_preimage q w.val_lt).mono
      rintro k ⟨hk, hout⟩
      refine ⟨hk, ?_⟩
      intro hn
      change (((q : ℕ) * k + w.val : ℕ) : ZMod (q : ℕ)) ∈
        outputMask A B q (((q : ℕ) * k + w.val) / (q : ℕ)) at hn
      apply hout
      simpa only [Nat.mul_add_div q.pos, Nat.div_eq_of_lt w.val_lt, add_zero,
        Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add,
        ZMod.natCast_zmod_val] using hn
    have hp := (hasDensity_iff_prefixCount D 0).mp hD
    have hcount : ∀ N, prefixCount D N = (escapingIndices A B q N w).card := by
      intro N
      unfold prefixCount escapingIndices
      congr 1
      ext k
      simp only [Finset.mem_filter, D, Set.mem_ofPred_eq]
    simpa only [hcount] using hp

theorem maskBranch_hasDensity (A B : Set ℕ) (s : ℝ) (h : MaskBranch A B s) :
    HasDensity (A + B) s := by
  obtain ⟨q, htransitions, hmean, hpacking⟩ := h
  have hW : HasDensity (blockSet q (outputMask A B q)) s :=
    (hasDensity_blockSet_iff q (outputMask A B q) s).mpr hmean
  have heq : DensityEquivalent (blockSet q (outputMask A B q)) (A + B) :=
    ⟨missing_output_negligible A B q htransitions, escaping_negligible_of_packing A B q hpacking⟩
  exact heq.hasDensity hW

theorem isErdos335Pair_of_maskBranch (A B : Set ℕ) (a b : ℝ)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (ha0 : 0 < a) (hb0 : 0 < b) (hA : HasDensity A a) (hB : HasDensity B b)
    (hmask : MaskBranch A B (a + b)) : IsErdos335Pair A B :=
  ⟨hApos, hBpos, a, b, ha0, hb0, hA, hB, maskBranch_hasDensity A B (a + b) hmask⟩

end Erdos335.Proposed
