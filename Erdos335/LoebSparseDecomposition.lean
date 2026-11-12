import Erdos335.LoebQuasiPeriodicData
import Erdos335.LoebFullSaturations

/-!
# Quasi-periodic data for a null extension in one coset
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance sparseDecompositionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_quasiPeriodicDecomposition_of_sparse_extension
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (Acore A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hAcorem : MeasurableSet Acore) (hAm : MeasurableSet A) (hAsub : Acore ⊆ A)
    (hmass : loebMeasure U hU A = loebMeasure U hU Acore)
    (hperiod : loebMeasure U hU ((Acore + (H : Set _)) \ Acore) = 0)
    (hupper : A ⊆ (Acore + (H : Set _)) ∪ (a +ᵥ (H : Set _)))
    (hne : (A \ (Acore + (H : Set _))).Nonempty) :
    ∃ d : QuasiPeriodicDecomposition (loebMeasure U hU) H A,
      d.active = A \ (Acore + (H : Set _)) ∧
      d.background = A ∩ (Acore + (H : Set _)) ∧ d.anchor = a ∧
      loebMeasure U hU d.active = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let P := Acore + (H : Set G)
  have hPm : MeasurableSet P :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos Acore
  have hPperiod : P + (H : Set G) = P := by
    dsimp only [P]
    rw [add_assoc, coe_add_coe]
  have hactive : A \ P ⊆ a +ᵥ (H : Set G) := by
    intro x hx
    exact (hupper hx.1).resolve_left hx.2
  have hpartition : A = (A ∩ P) ∪ (A \ P) := by
    ext x
    simp only [mem_union, mem_inter_iff, Set.mem_sdiff]
    tauto
  have hdisjoint : Disjoint ((A \ P) + (H : Set G)) (A ∩ P) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, k, hk, hky⟩ hx
    apply hy.2
    have hin : x + -k ∈ P + (H : Set G) :=
      add_mem_add hx.2 (H.neg_mem hk)
    rw [hPperiod] at hin
    change y + k = x at hky
    simpa only [← hky, add_neg_cancel_right] using hin
  let d : QuasiPeriodicDecomposition (loebMeasure U hU) H A := {
    active := A \ P
    background := A ∩ P
    anchor := a
    active_measurable := hAm.diff hPm
    background_measurable := hAm.inter hPm
    active_nonempty := hne
    partition := hpartition
    active_subset_coset := hactive
    separated := hdisjoint
    background_periodic := loeb_inter_saturation_background_periodic U hU q H Acore A hAsub hperiod
  }
  exact ⟨d, rfl, rfl, rfl, loeb_sparse_complement_measure_zero U hU q H Acore A hAcorem hAsub hmass⟩

end Erdos335.Loeb

end
