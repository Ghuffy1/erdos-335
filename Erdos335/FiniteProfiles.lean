import Erdos335.FiniteKneser

/-!
# Capacity equality for finite residue profiles

This is the finite step of the periodic-output reduction. Positive input masks
and literal input supports are distinguished, so sparse literal residues remain
in the cross-sum constraints.
-/

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Erdos335.FiniteProfiles

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem periodic_output_forces_full_inputs
    (P Q S T U : Finset G) (a b : G → ℝ)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPS : P ⊆ S) (hQT : Q ⊆ T)
    (hPT : P + T ⊆ U) (hSQ : S + Q ⊆ U)
    (hgap : ¬S + T ⊆ U)
    (ha : ∀ r ∈ P, a r ≤ 1) (hb : ∀ r ∈ Q, b r ≤ 1)
    (hmass : (∑ r ∈ P, a r) + (∑ r ∈ Q, b r) = U.card) :
    U.card = P.card + Q.card ∧
      (∀ r ∈ P, a r = 1) ∧ (∀ r ∈ Q, b r = 1) ∧
      (P + T) ∪ (S + Q) = U := by
  classical
  have hcore : P + Q ⊆ U :=
    (Finset.add_subset_add hPS (Finset.Subset.refl Q)).trans hSQ
  have haSum : (∑ r ∈ P, a r) ≤ (P.card : ℝ) := by
    simpa using Finset.sum_le_sum ha
  have hbSum : (∑ r ∈ Q, b r) ≤ (Q.card : ℝ) := by
    simpa using Finset.sum_le_sum hb
  have hcardLe : U.card ≤ P.card + Q.card := by
    have hreal : (U.card : ℝ) ≤ (P.card : ℝ) + Q.card := by linarith
    exact_mod_cast hreal
  have hcardGe : P.card + Q.card ≤ U.card := by
    by_contra h
    have hsmall : U.card < P.card + Q.card := by omega
    have hinside := FiniteKneser.extended_support_sum_subset hP hQ hcore hSQ hPT hsmall
    exact hgap (hinside.trans hcore)
  have hcard : U.card = P.card + Q.card := by omega
  have hcardReal : (U.card : ℝ) = (P.card : ℝ) + Q.card := by exact_mod_cast hcard
  have haExact : (∑ r ∈ P, a r) = (P.card : ℝ) := by linarith
  have hbExact : (∑ r ∈ Q, b r) = (Q.card : ℝ) := by linarith
  have haFull : ∀ r ∈ P, a r = 1 := by
    apply (Finset.sum_eq_sum_iff_of_le ha).mp
    simpa using haExact
  have hbFull : ∀ r ∈ Q, b r = 1 := by
    apply (Finset.sum_eq_sum_iff_of_le hb).mp
    simpa using hbExact
  have hbaseline : (P + T) ∪ (S + Q) = U := by
    have hsub : (P + T) ∪ (S + Q) ⊆ U := Finset.union_subset hPT hSQ
    by_contra hne
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    have hsmall : ((P + T) ∪ (S + Q)).card < P.card + Q.card := by omega
    have hcore' : P + Q ⊆ (P + T) ∪ (S + Q) :=
      (Finset.add_subset_add (Finset.Subset.refl P) hQT).trans Finset.subset_union_left
    have hinside := FiniteKneser.extended_support_sum_subset hP hQ hcore'
      Finset.subset_union_right Finset.subset_union_left hsmall
    exact hgap (hinside.trans (hcore'.trans hsub))
  exact ⟨hcard, haFull, hbFull, hbaseline⟩

end Erdos335.FiniteProfiles
