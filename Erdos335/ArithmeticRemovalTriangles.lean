import Erdos335.ArithmeticRemovalGraph

/-!
# Counting the triangles in the arithmetic removal graph
-/

set_option autoImplicit false

open Finset SimpleGraph

namespace Erdos335.ArithmeticRemoval

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def additiveTriples (A B C : Finset G) : Finset (G × G) :=
  (A ×ˢ B).filter fun p => p.1 + p.2 ∈ C

def triangleCoordinates : (G × G × G) ≃ (G × G × G) where
  toFun p := (p.1, p.2.1 - p.1, p.2.2 - p.2.1)
  invFun p := (p.1, p.1 + p.2.1, (p.1 + p.2.1) + p.2.2)
  left_inv := by
    rintro ⟨x, y, z⟩
    dsimp
    ext <;> abel
  right_inv := by
    rintro ⟨x, a, b⟩
    dsimp
    ext <;> abel

theorem card_triangleIndices (A B C : Finset G) :
    (triangleIndices A B C).card = Fintype.card G * (additiveTriples A B C).card := by
  classical
  calc
    (triangleIndices A B C).card = ((Finset.univ : Finset G) ×ˢ additiveTriples A B C).card := by
      apply Finset.card_equiv triangleCoordinates
      rintro ⟨x, y, z⟩
      have hsum : (y - x) + (z - y) = z - x := by abel
      simp only [mem_triangleIndices, triangleCoordinates, Equiv.coe_fn_mk, additiveTriples,
        mem_product, mem_univ, true_and, mem_filter, hsum]
      tauto
    _ = _ := by rw [Finset.card_product, Finset.card_univ]

theorem card_arithmetic_triangles (A B C : Finset G) :
    ((TripartiteFromTriangles.graph (triangleIndices A B C)).cliqueFinset 3).card =
      Fintype.card G * (additiveTriples A B C).card := by
  rw [card_cliqueFinset, card_triangleIndices]

end Erdos335.ArithmeticRemoval
