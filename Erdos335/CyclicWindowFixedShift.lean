import Erdos335.CyclicWindowRepresentatives
import Erdos335.DensityAlgebra

/-!
# Comparing a fixed integer shift with cyclic window translation
-/

set_option autoImplicit false

open Finset
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem fixed_shift_window_membership
    (A : Set ℕ) (start q u : ℕ) [NeZero q] (huq : u < q)
    (x : ZMod q) (hxu : u ≤ x.val) :
    x ∈ cyclicWindow (shift A u) start q ↔
      x ∈ cyclicWindow A start q + {(u : ZMod q)} := by
  classical
  have huval : (u : ZMod q).val = u := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt huq]
  have hval : (x - (u : ZMod q)).val = x.val - u := by
    rw [ZMod.val_sub (by rwa [huval]), huval]
  constructor
  · intro hx
    obtain ⟨n, hn, hnx⟩ := (Finset.mem_filter.mp hx).2
    change n + u = start + x.val at hnx
    have hnval : n = start + (x.val - u) := by omega
    refine Finset.mem_add.mpr ⟨x - (u : ZMod q), ?_, (u : ZMod q), Finset.mem_singleton_self _, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hval, ← hnval]
      exact hn
    · exact sub_add_cancel x _
  · intro hx
    obtain ⟨y, hy, z, hz, hsum⟩ := Finset.mem_add.mp hx
    have hz' : z = (u : ZMod q) := Finset.mem_singleton.mp hz
    subst z
    have hyx : y = x - (u : ZMod q) := (eq_sub_iff_add_eq).mpr hsum
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, start + y.val, (Finset.mem_filter.mp hy).2, ?_⟩
    change start + y.val + u = start + x.val
    rw [hyx, hval]
    omega

theorem fixed_shift_window_discrepancy_le
    (A : Set ℕ) (start q u : ℕ) [NeZero q] (huq : u < q) :
    ((cyclicWindow (shift A u) start q \ (cyclicWindow A start q + {(u : ZMod q)})) ∪
      ((cyclicWindow A start q + {(u : ZMod q)}) \ cyclicWindow (shift A u) start q)).card ≤ u := by
  classical
  suffices h : ((cyclicWindow (shift A u) start q \ (cyclicWindow A start q + {(u : ZMod q)})) ∪
      ((cyclicWindow A start q + {(u : ZMod q)}) \ cyclicWindow (shift A u) start q)).card ≤
      (Finset.range u).card by simpa using h
  apply Finset.card_le_card_of_injOn ZMod.val
  · intro x hx
    apply Finset.mem_range.mpr
    by_contra hnot
    have heq := fixed_shift_window_membership A start q u huq x (by omega)
    rcases Finset.mem_union.mp hx with hleft | hright
    · exact (Finset.mem_sdiff.mp hleft).2 (heq.mp (Finset.mem_sdiff.mp hleft).1)
    · exact (Finset.mem_sdiff.mp hright).2 (heq.mpr (Finset.mem_sdiff.mp hright).1)
  · intro x hx y hy hxy
    exact ZMod.val_injective q hxy

end Erdos335.IntermediateScale
