import Erdos335.LoebQuasiPeriodicBackground

/-!
# Quasi-periodic decomposition data under a null extension
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicExtensionDataLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_quasiPeriodicDecomposition_of_null_extension
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (A A' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hA'm : MeasurableSet A') (hAA' : A ⊆ A')
    (hmass : loebMeasure U hU A' = loebMeasure U hU A)
    (hbackground : loebMeasure U hU
      (((A' \ (p.anchor +ᵥ (H : Set _))) + (H : Set _)) \ (A' \ (p.anchor +ᵥ (H : Set _)))) = 0) :
    ∃ d : QuasiPeriodicDecomposition (loebMeasure U hU) H A',
      d.active = A' ∩ (p.anchor +ᵥ (H : Set _)) ∧
      d.background = A' \ (p.anchor +ᵥ (H : Set _)) ∧ d.anchor = p.anchor ∧
      d.active =ᵐ[loebMeasure U hU] p.active ∧ d.background =ᵐ[loebMeasure U hU] p.background := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let C := p.anchor +ᵥ (H : Set G)
  have hCm : MeasurableSet C := measurable_loeb_coset U hU H hHm p.anchor
  have hAm : MeasurableSet A := p.partition.symm ▸ (p.background_measurable.union p.active_measurable)
  have hzero : μ (A' \ A) = 0 := by
    rw [measure_sdiff hAA' hAm.nullMeasurableSet (measure_ne_top μ _), hmass, tsub_self]
  have hAE : A' =ᵐ[μ] A := (ae_le_set.mpr hzero).antisymm hAA'.eventuallySubset
  have hpartition : A' = (A' \ C) ∪ (A' ∩ C) := by
    ext x
    simp only [mem_union, Set.mem_sdiff, mem_inter_iff]
    tauto
  have hdisjoint : Disjoint ((A' ∩ C) + (H : Set G)) (A' \ C) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨y, ⟨_, ⟨k, hk, hky⟩⟩, l, hl, hlx⟩ ⟨_, hxout⟩
    apply hxout
    refine ⟨k + l, H.add_mem hk hl, ?_⟩
    change p.anchor + k = y at hky
    change y + l = x at hlx
    change p.anchor + (k + l) = x
    rw [← add_assoc, hky, hlx]
  have hnonempty : (A' ∩ C).Nonempty := by
    obtain ⟨x, hx⟩ := p.active_nonempty
    exact ⟨x, hAA' ((subset_union_right.trans p.partition.ge) hx), p.active_subset_coset hx⟩
  let d : QuasiPeriodicDecomposition μ H A' := {
    active := A' ∩ C
    background := A' \ C
    anchor := p.anchor
    active_measurable := hA'm.inter hCm
    background_measurable := hA'm.diff hCm
    active_nonempty := hnonempty
    partition := hpartition
    active_subset_coset := inter_subset_right
    separated := hdisjoint
    background_periodic := hbackground
  }
  have hactiveAE : d.active =ᵐ[μ] p.active := by
    rw [p.active_eq_inter_coset]
    filter_upwards [hAE] with x hx
    change (x ∈ A' ∧ x ∈ C) = (x ∈ A ∧ x ∈ C)
    rw [hx]
  have hbackgroundAE : d.background =ᵐ[μ] p.background := by
    rw [p.background_eq_sdiff_coset]
    filter_upwards [hAE] with x hx
    change (x ∈ A' ∧ x ∉ C) = (x ∈ A ∧ x ∉ C)
    rw [hx]
  exact ⟨d, rfl, rfl, rfl, hactiveAE, hbackgroundAE⟩

end Erdos335.Loeb

end
