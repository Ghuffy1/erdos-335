import Erdos335.ArithmeticRemovalLabels

/-!
# Counting removed edges by their additive labels
-/

set_option autoImplicit false

open Finset SimpleGraph Sum3
open scoped BigOperators

noncomputable section

namespace Erdos335.ArithmeticRemoval

theorem sum_fiber_card_le {I X Y : Type*} [DecidableEq I] [DecidableEq X] [DecidableEq Y]
    (S : Finset I) (T : I → Finset X) (f : I × X ↪ Y) (R : Finset Y)
    (hsub : ∀ i ∈ S, ∀ x ∈ T i, f (i, x) ∈ R) :
    (∑ i ∈ S, (T i).card) ≤ R.card := by
  let E : I → Finset Y := fun i => (T i).image (fun x => f (i, x))
  have hdisjoint : (S : Set I).PairwiseDisjoint E := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro y hyi hyj
    obtain ⟨x, hx, hxy⟩ := mem_image.mp hyi
    obtain ⟨z, hz, hzy⟩ := mem_image.mp hyj
    exact hij (congrArg Prod.fst (f.injective (hxy.trans hzy.symm)))
  have hcard (i : I) : (E i).card = (T i).card := by
    apply card_image_of_injective
    intro x y hxy
    exact congrArg Prod.snd (f.injective hxy)
  have hunion : (S.biUnion E).card = ∑ i ∈ S, (T i).card := by
    rw [card_biUnion hdisjoint]
    exact sum_congr rfl (fun i _ => hcard i)
  rw [← hunion]
  apply card_le_card
  intro y hy
  obtain ⟨i, hi, hy⟩ := mem_biUnion.mp hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact hsub i hi x hx

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def leftEdge : G × G ↪ Sym2 (G ⊕ G ⊕ G) where
  toFun p := s(in₀ p.2, in₁ (p.2 + p.1))
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hxy : x = y ∧ x + a = y + b := by
      simpa only [Sym2.eq_iff, Sum3.in₀, Sum3.in₁, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, false_and, or_false] using h
    rcases hxy with ⟨rfl, hab⟩
    exact Prod.ext (add_left_cancel hab) rfl

def rightEdge : G × G ↪ Sym2 (G ⊕ G ⊕ G) where
  toFun p := s(in₁ p.2, in₂ (p.2 + p.1))
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hxy : x = y ∧ x + a = y + b := by
      simpa only [Sym2.eq_iff, Sum3.in₁, Sum3.in₂, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, false_and, or_false] using h
    rcases hxy with ⟨rfl, hab⟩
    exact Prod.ext (add_left_cancel hab) rfl

def sumEdge : G × G ↪ Sym2 (G ⊕ G ⊕ G) where
  toFun p := s(in₀ p.2, in₂ (p.2 + p.1))
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hxy : x = y ∧ x + a = y + b := by
      simpa only [Sym2.eq_iff, Sum3.in₀, Sum3.in₂, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, false_and, or_false] using h
    rcases hxy with ⟨rfl, hab⟩
    exact Prod.ext (add_left_cancel hab) rfl

theorem sum_removedLeft_le (A B C S : Finset G) (H : SimpleGraph (G ⊕ G ⊕ G)) [DecidableRel H.Adj] :
    (∑ a ∈ S, (removedLeft A B C H a).card) ≤
      ((TripartiteFromTriangles.graph (triangleIndices A B C)).edgeFinset \ H.edgeFinset).card := by
  classical
  apply sum_fiber_card_le S (removedLeft A B C H) leftEdge
  intro a ha x hx
  simp only [removedLeft, mem_filter, mem_univ, true_and] at hx
  change s(in₀ x, in₁ (x + a)) ∈ _
  simpa only [mem_sdiff, mem_edgeFinset, mem_edgeSet] using hx

theorem sum_removedRight_le (A B C S : Finset G) (H : SimpleGraph (G ⊕ G ⊕ G)) [DecidableRel H.Adj] :
    (∑ b ∈ S, (removedRight A B C H b).card) ≤
      ((TripartiteFromTriangles.graph (triangleIndices A B C)).edgeFinset \ H.edgeFinset).card := by
  classical
  apply sum_fiber_card_le S (removedRight A B C H) rightEdge
  intro b hb y hy
  simp only [removedRight, mem_filter, mem_univ, true_and] at hy
  change s(in₁ y, in₂ (y + b)) ∈ _
  simpa only [mem_sdiff, mem_edgeFinset, mem_edgeSet] using hy

theorem sum_removedSum_le (A B C S : Finset G) (H : SimpleGraph (G ⊕ G ⊕ G)) [DecidableRel H.Adj] :
    (∑ c ∈ S, (removedSum A B C H c).card) ≤
      ((TripartiteFromTriangles.graph (triangleIndices A B C)).edgeFinset \ H.edgeFinset).card := by
  classical
  apply sum_fiber_card_le S (removedSum A B C H) sumEdge
  intro c hc x hx
  simp only [removedSum, mem_filter, mem_univ, true_and] at hx
  change s(in₀ x, in₂ (x + c)) ∈ _
  simpa only [mem_sdiff, mem_edgeFinset, mem_edgeSet] using hx

end Erdos335.ArithmeticRemoval

end
