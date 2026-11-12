import Erdos335.ArithmeticRemovalTriangles

/-!
# Applying triangle removal to the finite arithmetic graph
-/

set_option autoImplicit false

open Finset SimpleGraph

noncomputable section

namespace Erdos335.ArithmeticRemoval

def arithmeticRemovalBound (ε : ℝ) : ℝ := 27 * SimpleGraph.triangleRemovalBound (ε / 27)

theorem arithmeticRemovalBound_pos (ε : ℝ) (hε : 0 < ε) : 0 < arithmeticRemovalBound ε := by
  exact mul_pos (by norm_num) (SimpleGraph.triangleRemovalBound_pos (by positivity))

theorem exists_triangle_free_subgraph
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B C : Finset G) (ε : ℝ)
    (htriples : ((additiveTriples A B C).card : ℝ) <
      arithmeticRemovalBound ε * (Fintype.card G : ℝ) ^ 2) :
    ∃ H ≤ TripartiteFromTriangles.graph (triangleIndices A B C),
      ∃ _ : DecidableRel H.Adj,
        (((TripartiteFromTriangles.graph (triangleIndices A B C)).edgeFinset.card : ℝ) -
          H.edgeFinset.card) < (ε / 3) * (Fintype.card G : ℝ) ^ 2 ∧ H.CliqueFree 3 := by
  classical
  let graph := TripartiteFromTriangles.graph (triangleIndices A B C)
  have hN : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have htriangles : (graph.cliqueFinset 3).card <
      SimpleGraph.triangleRemovalBound (ε / 27) * (Fintype.card (G ⊕ G ⊕ G) : ℝ) ^ 3 := by
    dsimp only [graph]
    rw [card_arithmetic_triangles, Nat.cast_mul]
    simp only [Fintype.card_sum, Nat.cast_add]
    calc
      (Fintype.card G : ℝ) * (additiveTriples A B C).card <
          (Fintype.card G : ℝ) * (arithmeticRemovalBound ε * (Fintype.card G : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left htriples hN
      _ = _ := by unfold arithmeticRemovalBound; ring
  obtain ⟨H, hHG, hdec, hcut, hfree⟩ := SimpleGraph.triangle_removal htriangles
  refine ⟨H, hHG, hdec, ?_, hfree⟩
  convert hcut using 1
  simp only [Fintype.card_sum, Nat.cast_add, Nat.cast_pow]
  ring

end Erdos335.ArithmeticRemoval

end
