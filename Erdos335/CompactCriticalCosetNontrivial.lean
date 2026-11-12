import Erdos335.CompactDysonTransform

/-!
# A subgroup containing a positive critical pair is nontrivial
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem nontrivial_subgroup_of_positive_critical_cosets
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (H : AddSubgroup G) (A B : Set G) (a b : G)
    (hA : A ⊆ a +ᵥ (H : Set G)) (hB : B ⊆ b +ᵥ (H : Set G))
    (hApos : 0 < μ A) (hBpos : 0 < μ B) (hfull : μ (A + B) = μ A + μ B) :
    Nontrivial H := by
  by_contra hnon
  have : Subsingleton H := not_nontrivial_iff_subsingleton.mp hnon
  have hzero (h : H) : (h : G) = 0 := congrArg Subtype.val (Subsingleton.elim h 0)
  have hAsub : A ⊆ {a} := by
    intro x hx
    obtain ⟨h, hh, hhx⟩ := hA hx
    have hz : h = 0 := hzero ⟨h, hh⟩
    simpa only [hz, vadd_eq_add, add_zero, mem_singleton_iff] using hhx.symm
  have hBsub : B ⊆ {b} := by
    intro x hx
    obtain ⟨h, hh, hhx⟩ := hB hx
    have hz : h = 0 := hzero ⟨h, hh⟩
    simpa only [hz, vadd_eq_add, add_zero, mem_singleton_iff] using hhx.symm
  have hAsingle : A = {a} := by
    apply subset_antisymm hAsub
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hApos.ne'
    have hxa : x = a := hAsub hx
    exact singleton_subset_iff.mpr (hxa ▸ hx)
  have hBsingle : B = {b} := by
    apply subset_antisymm hBsub
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hBpos.ne'
    have hxb : x = b := hBsub hx
    exact singleton_subset_iff.mpr (hxb ▸ hx)
  rw [hAsingle, hBsingle, singleton_add_singleton] at hfull
  have htranslate : μ ({a + b} : Set G) = μ ({a} : Set G) := by
    have hset : ({a + b} : Set G) = b +ᵥ ({a} : Set G) := by simp [add_comm]
    rw [hset, vadd_set_eq_neg_preimage, measure_preimage_add]
  have hreal := congrArg ENNReal.toReal hfull
  rw [htranslate, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hreal
  have hbpositive : 0 < (μ ({b} : Set G)).toReal :=
    ENNReal.toReal_pos (hBsingle ▸ hBpos).ne' (measure_ne_top μ _)
  linarith

end Erdos335.Loeb
