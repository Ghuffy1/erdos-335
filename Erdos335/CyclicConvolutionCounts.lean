import Erdos335.CyclicWindowRepresentatives
import Erdos335.PopularSumsetRemoval

/-!
# Counting wrapped sums by an ordinary prefix convolution
-/

set_option autoImplicit false

open Finset
open scoped Pointwise

namespace Erdos335.IntermediateScale

noncomputable def prefixConvolutionCount (A B : Set ℕ) (x q : ℕ) : ℕ := by
  classical
  exact ((range q).filter (fun b => b ∈ B ∧ b ≤ x ∧ x - b ∈ A)).card

theorem prefixConvolutionCount_eq_zero (A B : Set ℕ) (x q : ℕ)
    (hx : x ∉ A + B) : prefixConvolutionCount A B x q = 0 := by
  classical
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro b hb hmem
  exact hx ⟨x - b, hmem.2.2, b, hmem.1, Nat.sub_add_cancel hmem.2.1⟩

theorem wrapped_representation_count_le (A B : Set ℕ) (start q : ℕ) [NeZero q]
    (c : ZMod q) (hc : c ∉ cyclicWindow (A + B) start q) :
    ArithmeticRemoval.representationCount (cyclicWindow A start q) (cyclicWindow B 0 q) c ≤
      prefixConvolutionCount A B (start + q + c.val) q := by
  classical
  have hcout : start + c.val ∉ A + B := by
    intro hmem
    exact hc (mem_filter.mpr ⟨mem_univ _, hmem⟩)
  unfold ArithmeticRemoval.representationCount prefixConvolutionCount
  apply card_le_card_of_injOn (fun p : ZMod q × ZMod q => p.2.val)
  · intro p hp
    obtain ⟨hpAB, hpc⟩ := mem_filter.mp hp
    obtain ⟨hpA, hpB⟩ := mem_product.mp hpAB
    have ha : start + p.1.val ∈ A := (mem_filter.mp hpA).2
    have hb : p.2.val ∈ B := by simpa using (mem_filter.mp hpB).2
    have haQ : p.1.val < q := ZMod.val_lt _
    have hbQ : p.2.val < q := ZMod.val_lt _
    have hcast : ((p.1.val + p.2.val : ℕ) : ZMod q) = c := by simpa using hpc
    have hmod : (p.1.val + p.2.val) % q = c.val := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast
    have hwrap : q ≤ p.1.val + p.2.val := by
      by_contra h
      have heq : p.1.val + p.2.val = c.val := by
        simpa only [Nat.mod_eq_of_lt (by omega : p.1.val + p.2.val < q)] using hmod
      apply hcout
      refine ⟨start + p.1.val, ha, p.2.val, hb, ?_⟩
      change (start + p.1.val) + p.2.val = start + c.val
      omega
    have hsum : p.1.val + p.2.val = q + c.val := by
      rw [Nat.mod_eq_sub_mod hwrap,
        Nat.mod_eq_of_lt (by omega : p.1.val + p.2.val - q < q)] at hmod
      omega
    apply mem_filter.mpr
    refine ⟨mem_range.mpr hbQ, hb, ?_, ?_⟩
    · change p.2.val ≤ start + q + c.val
      omega
    have heq : start + q + c.val - p.2.val = start + p.1.val := by omega
    rwa [heq]
  · intro p hp r hr heq
    have hb : p.2 = r.2 := ZMod.val_injective q heq
    have hpSum := (mem_filter.mp hp).2
    have hrSum := (mem_filter.mp hr).2
    have ha : p.1 = r.1 := by
      apply add_right_cancel (b := p.2)
      rw [← hb] at hrSum
      exact hpSum.trans hrSum.symm
    exact Prod.ext ha hb

end Erdos335.IntermediateScale
