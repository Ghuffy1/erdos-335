import Erdos335.LocalCompensation

/-!
# A finite profile with one exceptional coordinate
-/

set_option autoImplicit false

open scoped BigOperators

namespace Erdos335.FiniteProfiles

theorem sum_profile_with_one_exception {G : Type*} [Fintype G] [DecidableEq G]
    (R : Finset G) (i : G) (hi : i ∈ R) (f : G → ℝ)
    (hzero : ∀ r ∉ R, f r = 0) (hfull : ∀ r ∈ R.erase i, f r = 1) :
    (∑ r, f r) = (R.card : ℝ) - 1 + f i := by
  have hsumR : (∑ r ∈ R, f r) = ∑ r, f r :=
    Finset.sum_subset (Finset.subset_univ R) (fun r _ hr => hzero r hr)
  have hsumErase : (∑ r ∈ R.erase i, f r) = ((R.erase i).card : ℝ) := by
    calc
      (∑ r ∈ R.erase i, f r) = ∑ r ∈ R.erase i, (1 : ℝ) := Finset.sum_congr rfl hfull
      _ = _ := by simp
  have hsum := Finset.sum_erase_add R f hi
  have hcard : ((R.erase i).card : ℝ) + 1 = R.card := by
    exact_mod_cast Finset.card_erase_add_one hi
  rw [hsumErase, hsumR] at hsum
  linarith

end Erdos335.FiniteProfiles
