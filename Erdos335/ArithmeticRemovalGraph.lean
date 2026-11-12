import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

/-!
# The tripartite graph for finite arithmetic removal

This is the finite-group graph used to obtain the arithmetic removal
ingredient in the Ackelsberg--Richter intermediate-window construction.
-/

set_option autoImplicit false

open Finset SimpleGraph Sum3

namespace Erdos335.ArithmeticRemoval

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def triangleIndices (A B C : Finset G) : Finset (G × G × G) :=
  Finset.univ.filter fun p => p.2.1 - p.1 ∈ A ∧ p.2.2 - p.2.1 ∈ B ∧ p.2.2 - p.1 ∈ C

@[simp] theorem mem_triangleIndices (A B C : Finset G) (x y z : G) :
    (x, y, z) ∈ triangleIndices A B C ↔ y - x ∈ A ∧ z - y ∈ B ∧ z - x ∈ C := by
  simp [triangleIndices]

theorem triangleIndices_closed (A B C : Finset G) (x x' y y' z z' : G)
    (h₁ : (x', y, z) ∈ triangleIndices A B C)
    (h₂ : (x, y', z) ∈ triangleIndices A B C)
    (h₃ : (x, y, z') ∈ triangleIndices A B C) :
    (x, y, z) ∈ triangleIndices A B C := by
  rw [mem_triangleIndices] at *
  exact ⟨h₃.1, h₁.2.1, h₂.2.2⟩

theorem cliqueFinset_eq_map (A B C : Finset G) :
    (TripartiteFromTriangles.graph (triangleIndices A B C)).cliqueFinset 3 =
      (triangleIndices A B C).map TripartiteFromTriangles.toTriangle := by
  classical
  ext s
  rw [mem_cliqueFinset_iff, Finset.mem_map]
  constructor
  · intro hs
    rw [SimpleGraph.is3Clique_iff] at hs
    obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := hs
    obtain ⟨x, y, z, hset, hxy, hxz, hyz⟩ :=
      TripartiteFromTriangles.graph_triple huv huw hvw
    obtain ⟨z', hz'⟩ := TripartiteFromTriangles.Graph.in₀₁_iff.mp hxy
    obtain ⟨y', hy'⟩ := TripartiteFromTriangles.Graph.in₀₂_iff.mp hxz
    obtain ⟨x', hx'⟩ := TripartiteFromTriangles.Graph.in₁₂_iff.mp hyz
    exact ⟨(x, y, z), triangleIndices_closed A B C x x' y y' z z' hx' hy' hz', hset⟩
  · rintro ⟨p, hp, rfl⟩
    exact TripartiteFromTriangles.toTriangle_is3Clique hp

theorem card_cliqueFinset (A B C : Finset G) :
    ((TripartiteFromTriangles.graph (triangleIndices A B C)).cliqueFinset 3).card =
      (triangleIndices A B C).card := by
  rw [cliqueFinset_eq_map, Finset.card_map]

end Erdos335.ArithmeticRemoval
