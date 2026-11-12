import Erdos335.ArithmeticRemoval

/-!
# Passing from popular sums to literal sums after small deletions

This is the finite arithmetic removal ingredient used in the
Ackelsberg--Richter intermediate-window argument.
-/

set_option autoImplicit false

open Finset SimpleGraph
open scoped BigOperators Pointwise

noncomputable section

namespace Erdos335.ArithmeticRemoval

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def representationCount (A B : Finset G) (c : G) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 + p.2 = c)).card

def popularSum (A B : Finset G) (δ : ℝ) : Finset G := by
  classical
  exact univ.filter (fun c => δ * Fintype.card G < (representationCount A B c : ℝ))

def popularRemovalBound (ε : ℝ) : ℝ := arithmeticRemovalBound ε / 2

theorem popularRemovalBound_pos (ε : ℝ) (hε : 0 < ε) : 0 < popularRemovalBound ε := by
  exact div_pos (arithmeticRemovalBound_pos ε hε) (by norm_num)

theorem card_additiveTriples_eq_sum (A B C : Finset G) :
    (additiveTriples A B C).card = ∑ c ∈ C, representationCount A B c := by
  exact (sum_card_fiberwise_eq_card_filter (A ×ˢ B) C (fun p => p.1 + p.2)).symm

theorem nonpopular_triples_bound (A B : Finset G) (δ : ℝ) (hδ : 0 ≤ δ) :
    ((additiveTriples A B (univ \ popularSum A B δ)).card : ℝ) ≤
      δ * (Fintype.card G : ℝ) ^ 2 := by
  classical
  let C := univ \ popularSum A B δ
  have hpoint (c : G) (hc : c ∈ C) : (representationCount A B c : ℝ) ≤ δ * Fintype.card G := by
    have hnot := (mem_sdiff.mp hc).2
    simp only [popularSum, mem_filter, mem_univ, true_and] at hnot
    exact not_lt.mp hnot
  rw [card_additiveTriples_eq_sum, Nat.cast_sum]
  calc
    (∑ c ∈ C, (representationCount A B c : ℝ)) ≤ ∑ _c ∈ C, δ * Fintype.card G :=
      sum_le_sum hpoint
    _ = (C.card : ℝ) * (δ * Fintype.card G) := by simp
    _ ≤ (Fintype.card G : ℝ) * (δ * Fintype.card G) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ C) (by positivity)
    _ = _ := by ring

theorem popular_sumset_removal (A B : Finset G) (ε : ℝ) (hε : 0 < ε) :
    ∃ A' ⊆ A, ∃ B' ⊆ B,
      ((A \ A').card : ℝ) < ε * Fintype.card G ∧
      ((B \ B').card : ℝ) < ε * Fintype.card G ∧
      (((A' + B') \ popularSum A B (popularRemovalBound ε)).card : ℝ) < ε * Fintype.card G := by
  classical
  let δ := popularRemovalBound ε
  let S := popularSum A B δ
  let C := univ \ S
  have hδ : 0 < δ := popularRemovalBound_pos ε hε
  have hδlt : δ < arithmeticRemovalBound ε := by
    dsimp [δ, popularRemovalBound]
    linarith [arithmeticRemovalBound_pos ε hε]
  have hN : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have htriples : ((additiveTriples A B C).card : ℝ) <
      arithmeticRemovalBound ε * (Fintype.card G : ℝ) ^ 2 := by
    exact (nonpopular_triples_bound A B δ hδ.le).trans_lt
      (mul_lt_mul_of_pos_right hδlt (sq_pos_of_pos hN))
  obtain ⟨A', hA', B', hB', C', hC', hAcut, hBcut, hCcut, hnone⟩ := arithmetic_removal A B C ε htriples
  refine ⟨A', hA', B', hB', hAcut, hBcut, ?_⟩
  have hsub : (A' + B') \ S ⊆ C \ C' := by
    intro c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp (mem_sdiff.mp hc).1
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hc).2⟩, ?_⟩
    exact hnone a ha b hb
  exact (show (((A' + B') \ S).card : ℝ) ≤ (C \ C').card by
    exact_mod_cast card_le_card hsub).trans_lt hCcut

end Erdos335.ArithmeticRemoval

end
