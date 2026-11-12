import Erdos335.FiniteQuantizedRefinement

/-!
# Termination of finite energy refinement
-/

set_option autoImplicit false

open Finset
open scoped Classical

namespace Erdos335.IntermediateScale

theorem bounded_energy_selection {α : Type*} (allowed : Set α)
    (good : Finset α → Prop) (energy : Finset α → ℝ) (δ C : ℝ) (N : ℕ)
    (hzero : 0 ≤ energy ∅) (hbound : ∀ S : Finset α, (S : Set α) ⊆ allowed → energy S ≤ C)
    (hN : C < (N : ℝ) * δ)
    (hstep : ∀ S : Finset α, (S : Set α) ⊆ allowed → ¬good S →
      ∃ T : Finset α, (T : Set α) ⊆ allowed ∧ T.card ≤ S.card + 1 ∧ energy S + δ ≤ energy T) :
    ∃ S : Finset α, (S : Set α) ⊆ allowed ∧ S.card ≤ N ∧ good S := by
  have hiter (n : ℕ) :
      (∃ S : Finset α, (S : Set α) ⊆ allowed ∧ S.card ≤ n ∧ good S) ∨
      (∃ S : Finset α, (S : Set α) ⊆ allowed ∧ S.card ≤ n ∧ (n : ℝ) * δ ≤ energy S) := by
    induction n with
    | zero =>
      right
      exact ⟨∅, by simp, by simp, by simpa using hzero⟩
    | succ n ih =>
      rcases ih with ⟨S, hS, hcard, hg⟩ | ⟨S, hS, hcard, he⟩
      · left
        exact ⟨S, hS, hcard.trans (Nat.le_succ n), hg⟩
      · by_cases hg : good S
        · left
          exact ⟨S, hS, hcard.trans (Nat.le_succ n), hg⟩
        · obtain ⟨T, hT, hTcard, hTe⟩ := hstep S hS hg
          right
          refine ⟨T, hT, by omega, ?_⟩
          push_cast
          nlinarith
  rcases hiter N with hgood | ⟨S, hS, hcard, he⟩
  · exact hgood
  · have hb := hbound S hS
    linarith

end Erdos335.IntermediateScale
