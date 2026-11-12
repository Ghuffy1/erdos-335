import Erdos335.FiniteOneBaseline
import Erdos335.PeriodicOutput

/-!
# The finite contradiction required by two null prefixes

Private proof development. Verification status is recorded separately.
All hypotheses are finite support or normalized-cardinality statements.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Erdos335.FiniteKneser

theorem critical_cross_union_has_full_baseline
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (P Q R S U : Finset G)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hPR : P ⊆ R) (hQS : Q ⊆ S)
    (hunion : (P + S) ∪ (R + Q) = U)
    (hcard : U.card ≤ P.card + Q.card) (houtside : ¬R + S ⊆ U) :
    U.card = P.card + Q.card ∧ (P + S = U ∨ R + Q = U) := by
  have hleft : P + S ⊆ U := by
    rw [← hunion]
    exact Finset.subset_union_left
  have hright : R + Q ⊆ U := by
    rw [← hunion]
    exact Finset.subset_union_right
  have hcore : P + Q ⊆ U :=
    (Finset.add_subset_add (Finset.Subset.refl P) hQS).trans hleft
  have hcard' : U.card = P.card + Q.card := by
    apply Nat.le_antisymm hcard
    by_contra hnot
    have hsmall : U.card < P.card + Q.card := by omega
    have hfull : R + S ⊆ P + Q :=
      extended_support_sum_subset hP hQ hcore hright hleft hsmall
    exact houtside (hfull.trans hcore)
  exact ⟨hcard', one_baseline_eq_output P Q R S U hP hQ hPR hQS hunion hcard'⟩

end Erdos335.FiniteKneser

namespace Erdos335

theorem critical_residue_union_has_full_baseline
    (A B : Set ℕ) (m : ℕ+) (P Q U : Finset (ZMod (m : ℕ))) (a b : ℝ)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPR : P ⊆ residues (m : ℕ) A) (hQS : Q ⊆ residues (m : ℕ) B)
    (hunion : (P + residues (m : ℕ) B) ∪ (residues (m : ℕ) A + Q) = U)
    (ha : a = (P.card : ℝ) / (m : ℕ))
    (hb : b = (Q.card : ℝ) / (m : ℕ))
    (hbound : (U.card : ℝ) / (m : ℕ) ≤ a + b)
    (hgap : a + b < gamma A B) :
    (U.card : ℝ) / (m : ℕ) = a + b ∧
      (((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) = a + b ∨
        ((residues (m : ℕ) A + Q).card : ℝ) / (m : ℕ) = a + b) := by
  have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hmass : a + b = ((P.card + Q.card : ℕ) : ℝ) / (m : ℕ) := by
    rw [ha, hb, Nat.cast_add, add_div]
  have hcard : U.card ≤ P.card + Q.card := by
    rw [hmass] at hbound
    exact_mod_cast (div_le_div_iff_of_pos_right hm).mp hbound
  have houtside : ¬residues (m : ℕ) A + residues (m : ℕ) B ⊆ U := by
    intro hsub
    have hu := (gamma_le_of_residue_sum_subset A B U hsub).trans hbound
    exact not_le_of_gt hgap hu
  obtain ⟨hcard', hfull⟩ := FiniteKneser.critical_cross_union_has_full_baseline P Q
    (residues (m : ℕ) A) (residues (m : ℕ) B) U hP hQ hPR hQS hunion hcard houtside
  have hUmass : (U.card : ℝ) / (m : ℕ) = a + b := by rw [hcard', ← hmass]
  refine ⟨hUmass, ?_⟩
  rcases hfull with hleft | hright
  · exact Or.inl (by rw [hleft]; exact hUmass)
  · exact Or.inr (by rw [hright]; exact hUmass)

theorem strict_card_ratio_of_fractional_mass
    (h : ℕ+) (k n : ℕ) (x s : ℝ) (hx : 0 < x) (hx1 : x < 1)
    (hs : s = ((k : ℝ) + x) / (h : ℕ))
    (hbound : (n : ℝ) / (h : ℕ) ≤ s) :
    (n : ℝ) / (h : ℕ) < s := by
  have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  rcases lt_or_eq_of_le hbound with hlt | heq
  · exact hlt
  exfalso
  rw [hs] at heq
  have heq' : (n : ℝ) = (k : ℝ) + x := (div_left_inj' hh.ne').mp heq
  have hkn : k < n := by exact_mod_cast (show (k : ℝ) < (n : ℝ) by linarith)
  have hnk : n < k + 1 := by exact_mod_cast (show (n : ℝ) < (k : ℝ) + 1 by linarith)
  omega

end Erdos335
