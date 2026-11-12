import Erdos335.RepresentationBound

/-!
# A positive prefix profile determines the literal carrier of its partner
-/

set_option autoImplicit false

open scoped Pointwise

namespace Erdos335.FiniteProfiles

theorem carrier_eq_of_positive_partner {G : Type*} [AddCommGroup G] [DecidableEq G]
    (R S T : Finset G) (b c : G → ℝ) (hSR : S ⊆ R)
    (hcard : (S + T).card + 1 = S.card + T.card)
    (s t : G) (hs : s ∈ S) (ht : t ∈ T)
    (hpositive : ∀ y ∈ T, 0 < b y)
    (hfull : ∀ y ∈ T, y ≠ t → b y = 1)
    (hzero : ∀ u ∉ S + T, c u = 0)
    (hpartial : c (s + t) < 1)
    (htranslate : ∀ x ∈ R, ∀ y ∈ T, b y ≤ c (x + y)) : R = S := by
  have hsub : R + T ⊆ S + T := by
    intro u hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hu
    by_contra hn
    have hb := hpositive y hy
    have hc := htranslate x hx y hy
    rw [hzero _ hn] at hc
    linarith
  have hsum : R + T = S + T :=
    Finset.Subset.antisymm hsub (Finset.add_subset_add hSR (Finset.Subset.refl T))
  have hunique : ∀ x ∈ R, ∀ y ∈ T, x + y = s + t → x = s ∧ y = t := by
    intro x hx y hy hxy
    have hyt : y = t := by
      by_contra hn
      have hc := htranslate x hx y hy
      rw [hfull y hy hn, hxy] at hc
      linarith
    refine ⟨?_, hyt⟩
    rw [hyt] at hxy
    exact add_right_cancel hxy
  have hbound := FiniteKneser.card_sum_ge_of_unique_expression R T (hSR hs) ht hunique
  rw [hsum] at hbound
  have hle : R.card ≤ S.card := by omega
  exact (Finset.eq_of_subset_of_card_le hSR hle).symm

end Erdos335.FiniteProfiles
