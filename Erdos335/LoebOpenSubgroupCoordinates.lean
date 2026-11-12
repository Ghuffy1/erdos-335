import Erdos335.LoebSubgroupNormalization
import Erdos335.LoebHaar
import Erdos335.CompactOpenSubgroupHaar

/-!
# Cyclic Loeb coordinates for an open compact-factor subgroup
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance openCoordinatesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_loeb_open_subgroup_coordinates
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (H : OpenAddSubgroup K) :
    ∃ r : ℕ → ℕ+, ∃ p : ∀ n, ZMod (r n : ℕ) →+ ZMod (q n : ℕ),
      (∀ n, Function.Injective (p n)) ∧
      Set.range (productMapHom (U : Filter ℕ) p) = φ ⁻¹' (H : Set K) ∧
      0 < loebMeasure U hU (Set.range (productMapHom (U : Filter ℕ) p)) ∧
      ∃ ψ : (U : Filter ℕ).Product (fun n => ZMod (r n : ℕ)) →+ H,
        Measurable ψ ∧ Function.Surjective ψ ∧
        H.toAddSubgroup.subtype.comp ψ = φ.comp (productMapHom (U : Filter ℕ) p) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : ν.IsAddHaarMeasure := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  let L := H.toAddSubgroup.comap φ
  have hLm : MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) :=
    H.isOpen.measurableSet.preimage hφ
  have hLpos : 0 < μ (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
    change 0 < μ (φ ⁻¹' (H : Set K))
    rw [← Measure.map_apply hφ H.isOpen.measurableSet]
    exact H.isOpen.measure_pos ν ⟨0, H.zero_mem⟩
  obtain ⟨r, p, hp, hrange, he, _, _⟩ :=
    positive_loeb_subgroup_normalized_coordinates U hU q L hLm hLpos
  let e := productMapHom (U : Filter ℕ) p
  have hmem (x : (U : Filter ℕ).Product (fun n => ZMod (r n : ℕ))) : φ (e x) ∈ H := by
    change e x ∈ (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    rw [← hrange]
    exact ⟨x, rfl⟩
  let ψ : (U : Filter ℕ).Product (fun n => ZMod (r n : ℕ)) →+ H := {
    toFun := fun x => ⟨φ (e x), hmem x⟩
    map_zero' := Subtype.ext (by simp)
    map_add' := fun x y => Subtype.ext (by simp)
  }
  refine ⟨r, p, hp, hrange, ?_, ψ, ?_, ?_, ?_⟩
  · rwa [hrange]
  · exact (hφ.comp he.measurable).subtype_mk
  · intro z
    obtain ⟨y, hy⟩ := hsurj z.val
    have hyL : y ∈ (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
      change φ y ∈ H
      rw [hy]
      exact z.property
    obtain ⟨x, hx⟩ := hrange.symm ▸ hyL
    refine ⟨x, Subtype.ext ?_⟩
    change φ (e x) = z.val
    rw [hx, hy]
  · ext x
    rfl

end Erdos335.Loeb

end
