import Erdos335.NaturalCyclicProjection
import Erdos335.DensityAlgebra

/-!
# Comparing literal capacities through one exceptional residue
-/

set_option autoImplicit false

open Set
open scoped Pointwise Classical

namespace Erdos335

theorem natural_preimage_capacity (n h : ℕ+) (hd : (h : ℕ) ∣ (n : ℕ))
    (R : Finset (ZMod (h : ℕ))) :
    (((Finset.univ.filter (fun x : ZMod (n : ℕ) => Loeb.naturalCyclicProjection n h x ∈ R)).card : ℝ) /
      (n : ℕ)) = (R.card : ℝ) / (h : ℕ) := by
  let S := Finset.univ.filter (fun x : ZMod (n : ℕ) => Loeb.naturalCyclicProjection n h x ∈ R)
  have hsets : periodicSet S = periodicSet R := by
    ext k
    simp only [periodicSet, Set.mem_setOf_eq, S, Finset.mem_filter, Finset.mem_univ, true_and,
      Loeb.naturalCyclicProjection_natCast n h hd]
  exact (hasDensity_periodicSet S).unique (hsets ▸ hasDensity_periodicSet R)

theorem exceptional_fiber_card_bound
    {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [DecidableEq H]
    (φ : G →+ H) (Y Z : Finset G) (R T : Finset H) (a : G) (j : H)
    (hY : ∀ y ∈ Y, φ y ∈ T)
    (hfull : ∀ x : G, φ x ∈ R.erase (φ a + j) → x ∈ Z)
    (htranslate : ∀ y ∈ Y, a + y ∈ Z) :
    Y.card + (Finset.univ.filter (fun x : G => φ x ∈ R.erase (φ a + j))).card ≤
      Z.card + (Finset.univ.filter (fun x : G => φ x ∈ T.erase j)).card := by
  let I := Y.filter (fun y => φ y = j)
  let J := Y.filter (fun y => φ y ≠ j)
  let C := Finset.univ.filter (fun x : G => φ x ∈ R.erase (φ a + j))
  let D := Finset.univ.filter (fun x : G => φ x ∈ T.erase j)
  have hpart : I.card + J.card = Y.card := Finset.card_filter_add_card_filter_not _
  have hJ : J ⊆ D := by
    intro y hy
    obtain ⟨hyY, hyj⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hyj, hY y hyY⟩⟩
  have hsub : C ∪ I.image (fun y => a + y) ⊆ Z := by
    intro x hx
    rcases Finset.mem_union.mp hx with hC | hI
    · exact hfull x (Finset.mem_filter.mp hC).2
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hI
      exact htranslate y (Finset.mem_filter.mp hy).1
  have hdisjoint : Disjoint C (I.image (fun y => a + y)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hi
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
    have hne := (Finset.mem_erase.mp (Finset.mem_filter.mp hx).2).1
    have heq := (Finset.mem_filter.mp hy).2
    exact hne (by rw [map_add, heq])
  have hsize : C.card + I.card ≤ Z.card := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjoint,
      Finset.card_image_of_injective _ (fun _ _ hxy => add_left_cancel hxy)] at hc
    exact hc
  have hsmall := Finset.card_le_card hJ
  change Y.card + C.card ≤ Z.card + D.card
  omega

end Erdos335
