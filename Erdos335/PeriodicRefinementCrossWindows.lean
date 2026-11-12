import Erdos335.CyclicWindowRepresentatives
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# Literal cross-window translates

The element chosen in the second window may vary with the scale.  Translating
the entire first window by that element preserves its length exactly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open Erdos335.IntermediateScale
open scoped Pointwise

noncomputable section

namespace Erdos335.PeriodicRefinement

theorem residue_window_translate_subset
    (A B : Set ℕ) (m q : ℕ+) (r : ZMod (m : ℕ))
    (start b : ℕ) (hb : b ∈ B) :
    cyclicWindow {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r} start (q : ℕ) ⊆
      cyclicWindow {n : ℕ | n ∈ A + B ∧ (n : ZMod (m : ℕ)) = r + (b : ZMod (m : ℕ))}
        (start + b) (q : ℕ) := by
  classical
  intro z hz
  simp only [cyclicWindow, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_setOf_eq] at hz ⊢
  obtain ⟨ha, hr⟩ := hz
  constructor
  · have hsum : start + z.val + b ∈ A + B := ⟨start + z.val, ha, b, hb, rfl⟩
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum
  · calc
      ((start + b + z.val : ℕ) : ZMod (m : ℕ)) =
          ((start + z.val : ℕ) : ZMod (m : ℕ)) + (b : ZMod (m : ℕ)) := by
            push_cast
            ring
      _ = r + (b : ZMod (m : ℕ)) := by rw [hr]

theorem residue_window_translate_card_le
    (A B : Set ℕ) (m q : ℕ+) (r : ZMod (m : ℕ))
    (start b : ℕ) (hb : b ∈ B) :
    (cyclicWindow {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r} start (q : ℕ)).card ≤
      (cyclicWindow {n : ℕ | n ∈ A + B ∧ (n : ZMod (m : ℕ)) = r + (b : ZMod (m : ℕ))}
        (start + b) (q : ℕ)).card :=
  Finset.card_le_card (residue_window_translate_subset A B m q r start b hb)

theorem exists_literal_window_element
    (B : Set ℕ) (m q : ℕ+) (v : ZMod (m : ℕ)) (start : ℕ)
    (hpos : 0 < (cyclicWindow {n : ℕ | n ∈ B ∧ (n : ZMod (m : ℕ)) = v}
      start (q : ℕ)).card) :
    ∃ b ∈ B, (b : ZMod (m : ℕ)) = v ∧ start ≤ b ∧ b < start + (q : ℕ) := by
  classical
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  simp only [cyclicWindow, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_setOf_eq] at hz
  obtain ⟨hb, hv⟩ := hz
  exact ⟨start + z.val, hb, hv, Nat.le_add_right _ _, Nat.add_lt_add_left (ZMod.val_lt z) _⟩

theorem residue_cross_profile_le
    (A B : Set ℕ) (m : ℕ+) (q : ℕ → ℕ+) (r v : ZMod (m : ℕ))
    (start b : ℕ → ℕ) (a c : ℝ)
    (hb : ∀ᶠ n in atTop, b n ∈ B ∧ (b n : ZMod (m : ℕ)) = v)
    (ha : Tendsto (fun n => ((m : ℕ) : ℝ) *
      ((cyclicWindow {k : ℕ | k ∈ A ∧ (k : ZMod (m : ℕ)) = r}
        (start n) (q n : ℕ)).card : ℝ) / (q n : ℕ)) atTop (𝓝 a))
    (hc : Tendsto (fun n => ((m : ℕ) : ℝ) *
      ((cyclicWindow {k : ℕ | k ∈ A + B ∧ (k : ZMod (m : ℕ)) = r + v}
        (start n + b n) (q n : ℕ)).card : ℝ) / (q n : ℕ)) atTop (𝓝 c)) :
    a ≤ c := by
  apply le_of_tendsto_of_tendsto ha hc
  filter_upwards [hb] with n hn
  have hcard := residue_window_translate_card_le A B m (q n) r (start n) (b n) hn.1
  rw [hn.2] at hcard
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (Nat.cast_nonneg _)

end Erdos335.PeriodicRefinement

end
