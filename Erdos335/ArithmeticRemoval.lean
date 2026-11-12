import Erdos335.ArithmeticRemovalEdgeCounts

/-!
# Finite arithmetic removal

Triangle removal gives small edge deletion. Deleting labels that lose at
least one third of their edges removes every remaining additive triple.
The imported triangle removal proof is due to Yaël Dillies and Bhavik Mehta.
-/

set_option autoImplicit false

open Finset SimpleGraph
open scoped BigOperators

noncomputable section

namespace Erdos335.ArithmeticRemoval

theorem large_fiber_card_bound {I : Type*} [DecidableEq I]
    (S : Finset I) (f : I → ℕ) (N M : ℕ) (hsum : (∑ i ∈ S, f i) ≤ M) :
    (S.filter (fun i => N ≤ 3 * f i)).card * N ≤ 3 * M := by
  classical
  let T := S.filter (fun i => N ≤ 3 * f i)
  have hpoint : (∑ i ∈ T, N) ≤ ∑ i ∈ T, 3 * f i := by
    apply sum_le_sum
    intro i hi
    exact (mem_filter.mp hi).2
  have hsub : (∑ i ∈ T, f i) ≤ ∑ i ∈ S, f i :=
    sum_le_sum_of_subset (filter_subset _ _)
  calc
    T.card * N = ∑ _i ∈ T, N := by simp
    _ ≤ ∑ i ∈ T, 3 * f i := hpoint
    _ = 3 * ∑ i ∈ T, f i := (mul_sum T _ _).symm
    _ ≤ 3 * M := Nat.mul_le_mul_left 3 (hsub.trans hsum)

theorem large_fiber_small {I : Type*} [DecidableEq I]
    (S : Finset I) (f : I → ℕ) (N M : ℕ) (hN : 0 < N) (ε : ℝ)
    (hsum : (∑ i ∈ S, f i) ≤ M) (hM : (M : ℝ) < (ε / 3) * (N : ℝ) ^ 2) :
    ((S.filter (fun i => N ≤ 3 * f i)).card : ℝ) < ε * N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hbound : ((S.filter (fun i => N ≤ 3 * f i)).card : ℝ) * N ≤ 3 * (M : ℝ) := by
    exact_mod_cast large_fiber_card_bound S f N M hsum
  apply (mul_lt_mul_iff_of_pos_right hNR).mp
  nlinarith

theorem arithmetic_removal
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B C : Finset G) (ε : ℝ)
    (htriples : ((additiveTriples A B C).card : ℝ) <
      arithmeticRemovalBound ε * (Fintype.card G : ℝ) ^ 2) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C,
      ((A \ A').card : ℝ) < ε * Fintype.card G ∧
      ((B \ B').card : ℝ) < ε * Fintype.card G ∧
      ((C \ C').card : ℝ) < ε * Fintype.card G ∧
      ∀ a ∈ A', ∀ b ∈ B', a + b ∉ C' := by
  classical
  let graph := TripartiteFromTriangles.graph (triangleIndices A B C)
  obtain ⟨H, hHG, hdec, hcut, hfree⟩ := exists_triangle_free_subgraph A B C ε htriples
  let _ : DecidableRel H.Adj := hdec
  let M := (graph.edgeFinset \ H.edgeFinset).card
  let N := Fintype.card G
  let A' := A.filter (fun a => 3 * (removedLeft A B C H a).card < N)
  let B' := B.filter (fun b => 3 * (removedRight A B C H b).card < N)
  let C' := C.filter (fun c => 3 * (removedSum A B C H c).card < N)
  have hM : (M : ℝ) < (ε / 3) * (N : ℝ) ^ 2 := by
    have hsub : H.edgeFinset ⊆ graph.edgeFinset := edgeFinset_mono hHG
    have hcard : (M : ℝ) = (graph.edgeFinset.card : ℝ) - H.edgeFinset.card := by
      dsimp only [M]
      rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
    rw [hcard]
    exact hcut
  have hN : 0 < N := Fintype.card_pos
  refine ⟨A', filter_subset _ _, B', filter_subset _ _, C', filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · have heq : A \ A' = A.filter (fun a => N ≤ 3 * (removedLeft A B C H a).card) := by
      ext a
      simp only [A', mem_sdiff, mem_filter, not_and, not_lt]
      tauto
    rw [heq]
    exact large_fiber_small A (fun a => (removedLeft A B C H a).card) N M hN ε
      (sum_removedLeft_le A B C A H) hM
  · have heq : B \ B' = B.filter (fun b => N ≤ 3 * (removedRight A B C H b).card) := by
      ext b
      simp only [B', mem_sdiff, mem_filter, not_and, not_lt]
      tauto
    rw [heq]
    exact large_fiber_small B (fun b => (removedRight A B C H b).card) N M hN ε
      (sum_removedRight_le A B C B H) hM
  · have heq : C \ C' = C.filter (fun c => N ≤ 3 * (removedSum A B C H c).card) := by
      ext c
      simp only [C', mem_sdiff, mem_filter, not_and, not_lt]
      tauto
    rw [heq]
    exact large_fiber_small C (fun c => (removedSum A B C H c).card) N M hN ε
      (sum_removedSum_le A B C C H) hM
  · intro a ha b hb hc
    obtain ⟨haA, ha'⟩ := mem_filter.mp ha
    obtain ⟨hbB, hb'⟩ := mem_filter.mp hb
    obtain ⟨hcC, hc'⟩ := mem_filter.mp hc
    exact no_solution_of_small_removed A B C H hfree a b (a + b) haA hbB hcC rfl ha' hb' hc'

end Erdos335.ArithmeticRemoval

end
