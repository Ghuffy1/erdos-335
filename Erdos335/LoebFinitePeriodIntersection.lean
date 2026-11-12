import Erdos335.LoebSubgroupIndex
import Erdos335.LoebFiniteCosetCover

/-!
# Positive finite intersections of Loeb periods

A finite-index subgroup has positive outer measure because finitely many
translates cover the group. This gives positivity for intersections of
measurable positive periods.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance finitePeriodIntersectionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_finite_hom_kernel_outer_positive
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {F : Type*} [AddCommGroup F] [Finite F]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ F) :
    0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (φ.ker : Set _) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  by_contra h
  have hzero : μ (φ.ker : Set G) = 0 := le_antisymm (not_lt.mp h) bot_le
  obtain ⟨R, _, hcover⟩ := exists_finite_coset_cover φ (Set.univ : Set G)
  have hwhole : (Set.univ : Set G) ⊆ ⋃ r : R, (fun x => (r : G) + x) '' (φ.ker : Set G) := by
    intro x _
    have hx : x ∈ (Set.univ : Set G) + (φ.ker : Set G) :=
      ⟨x, mem_univ x, 0, φ.ker.zero_mem, add_zero x⟩
    rw [hcover] at hx
    obtain ⟨r, hr, k, hk, heq⟩ := hx
    exact mem_iUnion.mpr ⟨⟨r, hr⟩, ⟨k, hk, heq⟩⟩
  have hnull : μ (⋃ r : R, (fun x => (r : G) + x) '' (φ.ker : Set G)) = 0 := by
    apply measure_iUnion_null
    intro r
    rw [loebMeasure_image_add_left, hzero]
  have hbad := measure_mono_null hwhole hnull
  rw [loebMeasure_univ] at hbad
  exact one_ne_zero hbad

theorem loeb_positive_finite_index_subgroup
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) [H.FiniteIndex] :
    0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) := by
  simpa only [QuotientAddGroup.ker_mk'] using
    loeb_finite_hom_kernel_outer_positive U hU q (QuotientAddGroup.mk' H)

theorem loeb_positive_subgroup_intersection
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hKm : MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hKpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _)) :
    MeasurableSet ((H ⊓ K) : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU ((H ⊓ K) : Set _) := by
  have : H.FiniteIndex := ⟨(positive_measurable_subgroup_index U hU q H hHm hHpos).1.ne'⟩
  have : K.FiniteIndex := ⟨(positive_measurable_subgroup_index U hU q K hKm hKpos).1.ne'⟩
  exact ⟨hHm.inter hKm, loeb_positive_finite_index_subgroup U hU q (H ⊓ K)⟩

end Erdos335.Loeb

end
