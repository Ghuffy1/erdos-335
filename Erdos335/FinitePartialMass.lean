import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Equality of finite supports with one strictly partial coordinate
-/

set_option autoImplicit false

namespace Erdos335.FiniteProfiles

theorem support_eq_of_partial_mass {G : Type*} [DecidableEq G]
    (S R : Finset G) (hSR : S ⊆ R) (x y : ℝ)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1)
    (hmass : (S.card : ℝ) - 1 + x = (R.card : ℝ) - 1 + y) :
    S = R ∧ x = y := by
  have hle := Finset.card_le_card hSR
  have hcard : S.card = R.card := by
    by_contra hn
    have hlt : S.card + 1 ≤ R.card := by omega
    have hreal : (S.card : ℝ) + 1 ≤ R.card := by exact_mod_cast hlt
    linarith
  refine ⟨Finset.eq_of_subset_of_card_le hSR hcard.ge, ?_⟩
  rw [hcard] at hmass
  linarith

end Erdos335.FiniteProfiles
