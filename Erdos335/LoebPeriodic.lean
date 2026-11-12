import Erdos335.LoebTranslation

/-!
# Periods of quasi-periodic pieces

These measure identities implement the subgroup containment and background
reassembly used when a quasi-periodic decomposition is refined.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Finite (X n)]

theorem subgroup_le_of_positive_almost_periodic_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H K : AddSubgroup ((U : Filter ℕ).Product X))
    (A : Set ((U : Filter ℕ).Product X)) (a : (U : Filter ℕ).Product X)
    (hA : A ⊆ a +ᵥ (K : Set ((U : Filter ℕ).Product X)))
    (hpos : 0 < loebMeasure U hU A)
    (hperiod : loebMeasure U hU ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) = 0) :
    H ≤ K := by
  have hcoset {x : (U : Filter ℕ).Product X} (hx : x ∈ A) : x - a ∈ K := by
    obtain ⟨k, hk, rfl⟩ := hA hx
    change a + k - a ∈ K
    rw [add_sub_cancel_left]
    exact hk
  intro t ht
  by_contra hnot
  have hdisjoint {x : (U : Filter ℕ).Product X} (hx : x ∈ A) : t + x ∉ A := by
    intro htx
    have hmem := K.sub_mem (hcoset htx) (hcoset hx)
    have heq : (t + x - a) - (x - a) = t := by abel
    rw [heq] at hmem
    exact hnot hmem
  have hsub : (fun x => t + x) '' A ⊆
      (A + (H : Set ((U : Filter ℕ).Product X))) \ A := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨Set.mem_add.mpr ⟨x, hx, t, ht, add_comm x t⟩, hdisjoint hx⟩
  have hle := measure_mono hsub (μ := loebMeasure U hU)
  rw [loebMeasure_image_add_left, hperiod] at hle
  exact (not_le_of_gt hpos) hle

theorem almost_periodic_of_subgroup_le
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : Set ((U : Filter ℕ).Product X))
    (H K : AddSubgroup ((U : Filter ℕ).Product X)) (hHK : H ≤ K)
    (hperiod : loebMeasure U hU ((A + (K : Set ((U : Filter ℕ).Product X))) \ A) = 0) :
    loebMeasure U hU ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) = 0 := by
  apply le_antisymm _ bot_le
  change loebMeasure U hU ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) ≤ 0
  rw [← hperiod]
  apply measure_mono
  exact Set.sdiff_subset_sdiff_left (Set.add_subset_add (Subset.rfl) hHK)

theorem almost_periodic_union
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X))
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hA : loebMeasure U hU ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) = 0)
    (hB : loebMeasure U hU ((B + (H : Set ((U : Filter ℕ).Product X))) \ B) = 0) :
    loebMeasure U hU (((A ∪ B) + (H : Set ((U : Filter ℕ).Product X))) \ (A ∪ B)) = 0 := by
  have hsub : (((A ∪ B) + (H : Set ((U : Filter ℕ).Product X))) \ (A ∪ B)) ⊆
      ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) ∪
        ((B + (H : Set ((U : Filter ℕ).Product X))) \ B) := by
    rintro x ⟨hx, hn⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
    rcases hy with hy | hy
    · exact Or.inl ⟨Set.add_mem_add hy hz, fun h => hn (Or.inl h)⟩
    · exact Or.inr ⟨Set.add_mem_add hy hz, fun h => hn (Or.inr h)⟩
  apply le_antisymm _ bot_le
  calc
    _ ≤ loebMeasure U hU (((A + (H : Set ((U : Filter ℕ).Product X))) \ A) ∪
        ((B + (H : Set ((U : Filter ℕ).Product X))) \ B)) := measure_mono hsub
    _ ≤ loebMeasure U hU ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) +
        loebMeasure U hU ((B + (H : Set ((U : Filter ℕ).Product X))) \ B) := measure_union_le _ _
    _ = 0 := by rw [hA, hB, add_zero]

theorem almost_periodic_nested_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A C D : Set ((U : Filter ℕ).Product X)) (hCA : C ⊆ A) (hDC : D ⊆ C)
    (H K : AddSubgroup ((U : Filter ℕ).Product X)) (hHK : H ≤ K)
    (houter : loebMeasure U hU (((A \ C) + (K : Set ((U : Filter ℕ).Product X))) \ (A \ C)) = 0)
    (hinner : loebMeasure U hU (((C \ D) + (H : Set ((U : Filter ℕ).Product X))) \ (C \ D)) = 0) :
    loebMeasure U hU (((A \ D) + (H : Set ((U : Filter ℕ).Product X))) \ (A \ D)) = 0 := by
  have hsplit : A \ D = (A \ C) ∪ (C \ D) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union]
    constructor
    · rintro ⟨hx, hn⟩
      by_cases hc : x ∈ C
      · exact Or.inr ⟨hc, hn⟩
      · exact Or.inl ⟨hx, hc⟩
    · rintro (⟨hx, hn⟩ | ⟨hx, hn⟩)
      · exact ⟨hx, fun hd => hn (hDC hd)⟩
      · exact ⟨hCA hx, hn⟩
  rw [hsplit]
  exact almost_periodic_union U hU (A \ C) (C \ D) H
    (almost_periodic_of_subgroup_le U hU (A \ C) H K hHK houter) hinner

theorem proper_subgroup_of_positive_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H K : AddSubgroup ((U : Filter ℕ).Product X))
    (A B : Set ((U : Filter ℕ).Product X)) (a : (U : Filter ℕ).Product X)
    (hA : A ⊆ a +ᵥ (K : Set ((U : Filter ℕ).Product X)))
    (hB : B ⊆ a +ᵥ (K : Set ((U : Filter ℕ).Product X)))
    (hpos : 0 < loebMeasure U hU A) (hne : B.Nonempty)
    (hperiod : loebMeasure U hU ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) = 0)
    (hdisjoint : Disjoint (A + (H : Set ((U : Filter ℕ).Product X))) B) : H < K := by
  have hHK := subgroup_le_of_positive_almost_periodic_coset U hU H K A a hA hpos hperiod
  apply lt_of_le_of_ne hHK
  intro heq
  subst H
  have hneA : A.Nonempty := by
    by_contra h
    have hz : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [hz, measure_empty] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨x, hx⟩ := hneA
  obtain ⟨y, hy⟩ := hne
  obtain ⟨u, hu, hux⟩ := hA hx
  obtain ⟨v, hv, hvy⟩ := hB hy
  have hyx : y - x ∈ K := by
    have heq : y - x = v - u := by
      rw [← hux, ← hvy]
      simp only [vadd_eq_add]
      abel
    rw [heq]
    exact K.sub_mem hv hu
  have hyadd : y ∈ A + (K : Set ((U : Filter ℕ).Product X)) :=
    Set.mem_add.mpr ⟨x, hx, y - x, hyx, by abel⟩
  exact Set.disjoint_left.mp hdisjoint hyadd hy

end Erdos335.Loeb
