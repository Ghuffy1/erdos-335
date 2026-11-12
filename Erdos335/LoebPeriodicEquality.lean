import Erdos335.LoebOnePeriodicSummand

/-!
# Literal equality of positive-period sets

For sets invariant under a positive-measure subgroup, a null difference
is empty. An extension of exactly one coset's measure adds one coset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance periodicEqualityLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_periodic_subset_of_measure_sdiff_zero
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (S T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hS : S + (H : Set _) = S) (hT : T + (H : Set _) = T)
    (hzero : loebMeasure U hU (S \ T) = 0) : S ⊆ T := by
  intro x hxS
  by_contra hxT
  have hcoset : x +ᵥ (H : Set _) ⊆ S \ T := by
    rintro y ⟨k, hk, hky⟩
    constructor
    · rw [← hS]
      exact ⟨x, hxS, k, hk, hky⟩
    · intro hyT
      have hback : y + -k ∈ T + (H : Set _) := add_mem_add hyT (H.neg_mem hk)
      rw [hT] at hback
      change x + k = y at hky
      exact hxT (by simpa only [← hky, add_neg_cancel_right] using hback)
  have hz := measure_mono_null hcoset hzero
  rw [loebMeasure_coset U hU H x] at hz
  exact hHpos.ne' hz

theorem loeb_periodic_sets_eq_of_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (S T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hS : S + (H : Set _) = S) (hT : T + (H : Set _) = T)
    (heq : S =ᵐ[loebMeasure U hU] T) : S = T := by
  apply subset_antisymm
  · exact loeb_periodic_subset_of_measure_sdiff_zero U hU q H hHpos S T hS hT (ae_le_set.mp heq.le)
  · exact loeb_periodic_subset_of_measure_sdiff_zero U hU q H hHpos T S hT hS (ae_le_set.mp heq.symm.le)

theorem loeb_periodic_extension_by_one_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (S T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hSm : MeasurableSet S) (hTm : MeasurableSet T) (hST : S ⊆ T)
    (hS : S + (H : Set _) = S) (hT : T + (H : Set _) = T)
    (hmass : loebMeasure U hU T = loebMeasure U hU S +
      loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _)) :
    ∃ g ∉ S, T = S ∪ (g +ᵥ (H : Set _)) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hlt : μ S < μ T := by
    rw [hmass]
    exact ENNReal.lt_add_right (measure_ne_top μ S) hHpos.ne'
  have hnsub : ¬ T ⊆ S := fun hTS => (not_lt_of_ge (measure_mono hTS)) hlt
  obtain ⟨g, hgT, hgS⟩ := Set.not_subset.mp hnsub
  have hcosetT : g +ᵥ (H : Set G) ⊆ T := by
    rintro x ⟨k, hk, hkx⟩
    rw [← hT]
    exact ⟨g, hgT, k, hk, hkx⟩
  have hdisjoint : Disjoint S (g +ᵥ (H : Set G)) := by
    apply Set.disjoint_left.mpr
    rintro x hxS ⟨k, hk, hkx⟩
    have hback : x + -k ∈ S + (H : Set G) := add_mem_add hxS (H.neg_mem hk)
    rw [hS] at hback
    change g + k = x at hkx
    exact hgS (by simpa only [← hkx, add_neg_cancel_right] using hback)
  have hcosetm := measurable_loeb_coset U hU H hHm g
  have hUm : MeasurableSet (S ∪ (g +ᵥ (H : Set G))) := hSm.union hcosetm
  have hUT : S ∪ (g +ᵥ (H : Set G)) ⊆ T := union_subset hST hcosetT
  have hUmass : μ (S ∪ (g +ᵥ (H : Set G))) = μ T := by
    rw [measure_union hdisjoint hcosetm, loebMeasure_coset U hU H g]
    exact hmass.symm
  have hzero : μ (T \ (S ∪ (g +ᵥ (H : Set G)))) = 0 := by
    rw [measure_sdiff hUT hUm.nullMeasurableSet (measure_ne_top μ _), hUmass, tsub_self]
  have hcosetperiod : (g +ᵥ (H : Set G)) + (H : Set G) = g +ᵥ (H : Set G) := by
    apply subset_antisymm
    · rintro x ⟨y, ⟨k, hk, rfl⟩, l, hl, rfl⟩
      exact ⟨k + l, H.add_mem hk hl, by simp [vadd_eq_add, add_assoc]⟩
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hUperiod : (S ∪ (g +ᵥ (H : Set G))) + (H : Set G) = S ∪ (g +ᵥ (H : Set G)) := by
    rw [union_add, hS, hcosetperiod]
  refine ⟨g, hgS, subset_antisymm ?_ hUT⟩
  exact loeb_periodic_subset_of_measure_sdiff_zero U hU q H hHpos T
    (S ∪ (g +ᵥ (H : Set G))) hT hUperiod hzero

end Erdos335.Loeb

end
