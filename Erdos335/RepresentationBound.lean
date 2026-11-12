import Erdos335.FiniteKneser

/-!
# Representation counts from finite Kneser

The stabilizer hole count bounds the deficit by the number of expressions
of each actual sum. The unique-expression case is used in the local finite
template reductions.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Erdos335.FiniteKneser

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem neg_mem_addStab {C : Finset G} (hC : C.Nonempty) {h : G}
    (hh : h ∈ C.addStab) : -h ∈ C.addStab := by
  apply (Finset.mem_addStab hC).mpr
  have heq := (Finset.mem_addStab hC).mp hh
  calc
    -h +ᵥ C = -h +ᵥ (h +ᵥ C) := congrArg (fun X : Finset G => -h +ᵥ X) heq.symm
    _ = C := neg_vadd_vadd h C

theorem deficit_le_representation_count (A B : Finset G) {z : G}
    (hz : z ∈ A + B) :
    A.card + B.card ≤ (A + B).card +
      ((A.product B).filter (fun p => p.1 + p.2 = z)).card := by
  classical
  by_cases hsmall : (A + B).card < A.card + B.card
  swap
  · omega
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
  let H := (A + B).addStab
  let good := H.filter (fun h => a + h ∈ A ∧ b - h ∈ B)
  let badA := H.filter (fun h => a + h ∉ A)
  let badB := H.filter (fun h => b - h ∉ B)
  have hsum : (A + B).Nonempty := ⟨a + b, Finset.add_mem_add ha hb⟩
  have hzero : (0 : G) ∈ H := Finset.zero_mem_addStab.mpr hsum
  have hAsub : A ⊆ A + H := subset_add_stabilizer_right A hzero
  have hBsub : B ⊆ B + H := subset_add_stabilizer_right B hzero
  have hAholes : badA.card ≤ (A + H).card - A.card := by
    rw [← Finset.card_sdiff_of_subset hAsub]
    apply Finset.card_le_card_of_injOn (fun h => a + h)
    · intro h hh
      obtain ⟨hhH, hhA⟩ := Finset.mem_filter.mp hh
      exact Finset.mem_sdiff.mpr ⟨Finset.add_mem_add ha hhH, hhA⟩
    · intro h₁ hh₁ h₂ hh₂ heq
      exact add_left_cancel heq
  have hBholes : badB.card ≤ (B + H).card - B.card := by
    rw [← Finset.card_sdiff_of_subset hBsub]
    apply Finset.card_le_card_of_injOn (fun h => b - h)
    · intro h hh
      obtain ⟨hhH, hhB⟩ := Finset.mem_filter.mp hh
      have hneg : -h ∈ H := neg_mem_addStab hsum hhH
      exact Finset.mem_sdiff.mpr ⟨by simpa only [sub_eq_add_neg] using Finset.add_mem_add hb hneg, hhB⟩
    · intro h₁ hh₁ h₂ hh₂ heq
      have h := congrArg (fun x => b - x) heq
      simpa only [sub_sub_cancel] using h
  have hcover : H ⊆ good ∪ badA ∪ badB := by
    intro h hh
    by_cases hA : a + h ∈ A
    · by_cases hB : b - h ∈ B
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hh, hA, hB⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hh, hB⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hh, hA⟩))
  have hcoverCard : H.card ≤ good.card + badA.card + badB.card := by
    calc
      H.card ≤ (good ∪ badA ∪ badB).card := Finset.card_le_card hcover
      _ ≤ (good ∪ badA).card + badB.card := Finset.card_union_le _ _
      _ ≤ good.card + badA.card + badB.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hgood : good.card ≤ ((A.product B).filter (fun p => p.1 + p.2 = a + b)).card := by
    apply Finset.card_le_card_of_injOn (fun h => (a + h, b - h))
    · intro h hh
      obtain ⟨hhH, hhA, hhB⟩ := Finset.mem_filter.mp hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hhA, hhB⟩, ?_⟩
      dsimp only
      abel
    · intro h₁ hh₁ h₂ hh₂ heq
      exact add_left_cancel (congrArg Prod.fst heq)
  have hidentity := critical_card_identity ⟨a, ha⟩ ⟨b, hb⟩ hsmall
  have hAc := Finset.card_le_card hAsub
  have hBc := Finset.card_le_card hBsub
  change (A + H).card + (B + H).card = (A + B).card + H.card at hidentity
  omega

theorem card_sum_ge_of_unique_expression (A B : Finset G) {a b : G}
    (ha : a ∈ A) (hb : b ∈ B)
    (hunique : ∀ x ∈ A, ∀ y ∈ B, x + y = a + b → x = a ∧ y = b) :
    A.card + B.card ≤ (A + B).card + 1 := by
  classical
  have hrepr : (A.product B).filter (fun p => p.1 + p.2 = a + b) = {(a, b)} := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpAB, hpsum⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hpAB
      obtain ⟨hxa, hyb⟩ := hunique p.1 hpa p.2 hpb hpsum
      exact Finset.mem_singleton.mpr (Prod.ext hxa hyb)
    · intro hp
      have heq : p = (a, b) := Finset.mem_singleton.mp hp
      subst p
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  have h := deficit_le_representation_count A B (Finset.add_mem_add ha hb)
  simpa only [hrepr, Finset.card_singleton] using h

theorem card_of_unique_extra_sum (R S T : Finset G) (hSR : S ⊂ R)
    {a b : G} (ha : a ∈ R) (hb : b ∈ T)
    (hunique : ∀ x ∈ R, ∀ y ∈ T, x + y = a + b → x = a ∧ y = b)
    (hsum : (R + T).card = S.card + T.card) : R.card = S.card + 1 := by
  have hupper := card_sum_ge_of_unique_expression R T ha hb hunique
  have hlower := Finset.card_lt_card hSR
  rw [hsum] at hupper
  omega

end Erdos335.FiniteKneser
