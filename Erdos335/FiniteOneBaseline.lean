import Erdos335.FiniteKneser

/-!
# One cross-sum saturates a critical union of two cross-sums

Strict finite completion forces one of the two cross-sums to fill the union.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Erdos335.FiniteKneser

theorem one_baseline_eq_output
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (P Q R S U : Finset G)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPR : P ⊆ R) (hQS : Q ⊆ S)
    (hunion : (P + S) ∪ (R + Q) = U)
    (hcard : U.card = P.card + Q.card) :
    P + S = U ∨ R + Q = U := by
  classical
  by_cases hleft : P + S = U
  · exact Or.inl hleft
  · have hWsub : P + S ⊆ U := by
      rw [← hunion]
      exact Finset.subset_union_left
    have hproper : P + S ⊂ U :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hWsub, hleft⟩
    have hsmall : (P + S).card < P.card + Q.card := by
      calc
        (P + S).card < U.card := Finset.card_lt_card hproper
        _ = P.card + Q.card := hcard
    have hcore : P + Q ⊆ P + S :=
      Finset.add_subset_add (Finset.Subset.refl P) hQS
    have hback : P + S ⊆ P + Q :=
      extended_support_sum_subset (P := P) (Q := Q) (S := P) (T := S) (U := P + S)
        hP hQ hcore hcore (Finset.Subset.refl (P + S)) hsmall
    have hwithin : P + S ⊆ R + Q :=
      hback.trans (Finset.add_subset_add hPR (Finset.Subset.refl Q))
    have hcollapse : (P + S) ∪ (R + Q) = R + Q := Finset.union_eq_right.mpr hwithin
    exact Or.inr (hcollapse.symm.trans hunion)

end Erdos335.FiniteKneser
