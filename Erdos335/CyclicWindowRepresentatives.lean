import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Restoring literal representatives to cyclic windows

A fixed positive integer shift adds at most its own size to the error made
by wrapping a window into a cyclic group. This controls the restoration of
finite initial subsets after applying arithmetic removal.
-/

set_option autoImplicit false

open Finset
open scoped Pointwise

namespace Erdos335.IntermediateScale

noncomputable def cyclicWindow (A : Set ℕ) (start q : ℕ) [NeZero q] : Finset (ZMod q) := by
  classical
  exact univ.filter fun x => start + x.val ∈ A

theorem fixed_shift_window_error_le (A B : Set ℕ) (start q b : ℕ) [NeZero q]
    (hb : b ∈ B) (hbq : b < q) :
    (((cyclicWindow A start q + {(b : ZMod q)}) \ cyclicWindow (A + B) start q).card) ≤ b := by
  classical
  suffices h : (((cyclicWindow A start q + {(b : ZMod q)}) \
      cyclicWindow (A + B) start q).card) ≤ (range b).card by simpa using h
  apply Finset.card_le_card_of_injOn ZMod.val
  · intro z hz
    obtain ⟨hzsum, hzout⟩ := mem_sdiff.mp hz
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp hzsum
    have hyb : y = (b : ZMod q) := mem_singleton.mp hy
    subst y
    subst z
    apply mem_range.mpr
    have hxA : start + x.val ∈ A := (mem_filter.mp hx).2
    have hxq : x.val < q := ZMod.val_lt x
    have heq : x + (b : ZMod q) = ((x.val + b : ℕ) : ZMod q) := by
      simp
    rw [heq, ZMod.val_natCast]
    by_cases hwrap : x.val + b < q
    · have hval : (x + (b : ZMod q)).val = x.val + b := by
        rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt hwrap]
      have hmem : x + (b : ZMod q) ∈ cyclicWindow (A + B) start q := by
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        rw [hval]
        exact ⟨start + x.val, hxA, b, hb, Nat.add_assoc _ _ _⟩
      exact (hzout hmem).elim
    · have hsub : x.val + b - q < b := by omega
      have hmod : (x.val + b) % q = x.val + b - q := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      simpa only [hmod] using hsub
  · intro x hx y hy hxy
    exact ZMod.val_injective q hxy

theorem finite_representative_window_error_le (A B : Set ℕ) (start q : ℕ) [NeZero q]
    (F : Finset ℕ) (hF : ∀ b ∈ F, b ∈ B ∧ b < q) :
    (((cyclicWindow A start q + F.image (fun b : ℕ => (b : ZMod q))) \
      cyclicWindow (A + B) start q).card) ≤ ∑ b ∈ F, b := by
  classical
  let errors := fun b : ℕ => (cyclicWindow A start q + {(b : ZMod q)}) \
    cyclicWindow (A + B) start q
  have hsub : (cyclicWindow A start q + F.image (fun b : ℕ => (b : ZMod q))) \
      cyclicWindow (A + B) start q ⊆ F.biUnion errors := by
    intro z hz
    obtain ⟨hsum, hout⟩ := mem_sdiff.mp hz
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp hsum
    obtain ⟨b, hb, hby⟩ := mem_image.mp hy
    apply mem_biUnion.mpr
    refine ⟨b, hb, mem_sdiff.mpr ⟨?_, hout⟩⟩
    apply mem_add.mpr
    exact ⟨x, hx, y, mem_singleton.mpr hby.symm, hxy⟩
  calc
    _ ≤ (F.biUnion errors).card := card_le_card hsub
    _ ≤ ∑ b ∈ F, (errors b).card := card_biUnion_le
    _ ≤ ∑ b ∈ F, b := sum_le_sum fun b hb =>
      fixed_shift_window_error_le A B start q b (hF b hb).1 (hF b hb).2

theorem restored_representatives_error_le (A B : Set ℕ) (start q : ℕ) [NeZero q]
    (A' B' : Finset (ZMod q)) (hA' : A' ⊆ cyclicWindow A start q)
    (F : Finset ℕ) (hF : ∀ b ∈ F, b ∈ B ∧ b < q) :
    (((A' + (B' ∪ F.image (fun b : ℕ => (b : ZMod q)))) \
      cyclicWindow (A + B) start q).card) ≤
    (((A' + B') \ cyclicWindow (A + B) start q).card) + ∑ b ∈ F, b := by
  classical
  have hsub : (A' + (B' ∪ F.image (fun b : ℕ => (b : ZMod q)))) \
      cyclicWindow (A + B) start q ⊆
      ((A' + B') \ cyclicWindow (A + B) start q) ∪
      ((cyclicWindow A start q + F.image (fun b : ℕ => (b : ZMod q))) \
        cyclicWindow (A + B) start q) := by
    intro z hz
    obtain ⟨hsum, hout⟩ := mem_sdiff.mp hz
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp hsum
    rcases mem_union.mp hy with hy | hy
    · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_add.mpr ⟨x, hx, y, hy, hxy⟩, hout⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_add.mpr ⟨x, hA' hx, y, hy, hxy⟩, hout⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (finite_representative_window_error_le A B start q F hF) _))

end Erdos335.IntermediateScale
