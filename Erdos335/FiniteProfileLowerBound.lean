import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# A lower bound on every occupied coordinate of a finite profile
-/

set_option autoImplicit false

open scoped BigOperators

namespace Erdos335.FiniteProfiles

theorem coordinate_ge_total_sub_card {G : Type*} [Fintype G] [DecidableEq G]
    (T : Finset G) (f : G → ℝ)
    (hzero : ∀ r ∉ T, f r = 0) (hupper : ∀ r, f r ≤ 1)
    (r : G) (hr : r ∈ T) :
    (∑ v, f v) - ((T.card : ℝ) - 1) ≤ f r := by
  have hsum : (∑ v, f v) = ∑ v ∈ T, f v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ T)
    intro v _ hv
    exact hzero v hv
  have hbound : (∑ v ∈ T.erase r, f v) ≤ ((T.erase r).card : ℝ) := by
    calc
      (∑ v ∈ T.erase r, f v) ≤ ∑ _v ∈ T.erase r, (1 : ℝ) :=
        Finset.sum_le_sum (fun v _ => hupper v)
      _ = _ := by simp
  have hsplit := Finset.sum_erase_add T f hr
  have hcard : ((T.erase r).card : ℝ) + 1 = T.card := by
    exact_mod_cast Finset.card_erase_add_one hr
  rw [← hsum] at hsplit
  linarith

end Erdos335.FiniteProfiles
