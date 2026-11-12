import Erdos335.ArithmeticRemovalReduction

/-!
# Removing labels after a triangle-free graph restriction
-/

set_option autoImplicit false

open Finset SimpleGraph Sum3

noncomputable section

namespace Erdos335.ArithmeticRemoval

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def removedLeft (A B C : Finset G) (H : SimpleGraph (G ⊕ G ⊕ G)) (a : G) : Finset G := by
  classical
  exact univ.filter fun x =>
    (TripartiteFromTriangles.graph (triangleIndices A B C)).Adj (in₀ x) (in₁ (x + a)) ∧
      ¬H.Adj (in₀ x) (in₁ (x + a))

def removedRight (A B C : Finset G) (H : SimpleGraph (G ⊕ G ⊕ G)) (b : G) : Finset G := by
  classical
  exact univ.filter fun y =>
    (TripartiteFromTriangles.graph (triangleIndices A B C)).Adj (in₁ y) (in₂ (y + b)) ∧
      ¬H.Adj (in₁ y) (in₂ (y + b))

def removedSum (A B C : Finset G) (H : SimpleGraph (G ⊕ G ⊕ G)) (c : G) : Finset G := by
  classical
  exact univ.filter fun x =>
    (TripartiteFromTriangles.graph (triangleIndices A B C)).Adj (in₀ x) (in₂ (x + c)) ∧
      ¬H.Adj (in₀ x) (in₂ (x + c))

theorem exists_avoiding_three_sets (L R S : Finset G) (a : G)
    (hsmall : L.card + R.card + S.card < Fintype.card G) :
    ∃ x : G, x ∉ L ∧ x + a ∉ R ∧ x ∉ S := by
  classical
  let T := (L ∪ R.image (fun y => y - a)) ∪ S
  have hT : T.card ≤ L.card + R.card + S.card := by
    have h₁ := card_union_le (L ∪ R.image (fun y => y - a)) S
    have h₂ := card_union_le L (R.image (fun y => y - a))
    have h₃ : (R.image (fun y => y - a)).card ≤ R.card := card_image_le
    dsimp only [T]
    omega
  have hnot : ¬(univ : Finset G) ⊆ T := by
    intro h
    have hle := card_le_card h
    rw [card_univ] at hle
    omega
  obtain ⟨x, _, hx⟩ := not_subset.mp hnot
  refine ⟨x, ?_, ?_, ?_⟩
  · exact fun h => hx (mem_union_left _ (mem_union_left _ h))
  · intro h
    apply hx
    exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨x + a, h, by abel⟩))
  · exact fun h => hx (mem_union_right _ h)

theorem no_solution_of_small_removed
    (A B C : Finset G) (H : SimpleGraph (G ⊕ G ⊕ G)) (hH : H.CliqueFree 3)
    (a b c : G) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C) (habc : a + b = c)
    (hleft : 3 * (removedLeft A B C H a).card < Fintype.card G)
    (hright : 3 * (removedRight A B C H b).card < Fintype.card G)
    (hsum : 3 * (removedSum A B C H c).card < Fintype.card G) : False := by
  classical
  subst c
  have hsmall : (removedLeft A B C H a).card + (removedRight A B C H b).card +
      (removedSum A B C H (a + b)).card < Fintype.card G := by omega
  obtain ⟨x, hxleft, hxright, hxsum⟩ := exists_avoiding_three_sets
    (removedLeft A B C H a) (removedRight A B C H b) (removedSum A B C H (a + b)) a hsmall
  have hindex : (x, x + a, x + (a + b)) ∈ triangleIndices A B C := by
    rw [mem_triangleIndices]
    have h₁ : x + a - x = a := by abel
    have h₂ : x + (a + b) - (x + a) = b := by abel
    have h₃ : x + (a + b) - x = a + b := by abel
    rw [h₁, h₂, h₃]
    exact ⟨ha, hb, hc⟩
  have h01 : H.Adj (in₀ x) (in₁ (x + a)) := by
    by_contra hn
    apply hxleft
    simp only [removedLeft, mem_filter, mem_univ, true_and]
    exact ⟨TripartiteFromTriangles.Rel.in₀₁ hindex, hn⟩
  have h02 : H.Adj (in₀ x) (in₂ (x + (a + b))) := by
    by_contra hn
    apply hxsum
    simp only [removedSum, mem_filter, mem_univ, true_and]
    exact ⟨TripartiteFromTriangles.Rel.in₀₂ hindex, hn⟩
  have h12 : H.Adj (in₁ (x + a)) (in₂ (x + (a + b))) := by
    by_contra hn
    apply hxright
    simp only [removedRight, mem_filter, mem_univ, true_and]
    have heq : x + a + b = x + (a + b) := add_assoc _ _ _
    rw [heq]
    exact ⟨TripartiteFromTriangles.Rel.in₁₂ hindex, hn⟩
  have hclique : H.IsNClique 3 {in₀ x, in₁ (x + a), in₂ (x + (a + b))} :=
    is3Clique_triple_iff.mpr ⟨h01, h02, h12⟩
  exact hclique.not_cliqueFree hH

end Erdos335.ArithmeticRemoval

end
