import Erdos335.LoebEnvelopeStabilizer

/-!
# The stabilizer of a finite-period saturation
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance coarsenedPeriodLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_saturation_stabilizer
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let K := AddAction.stabilizer G (C + (H : Set G))
    MeasurableSet (K : Set G) ∧ 0 < loebMeasure U hU (K : Set G) ∧
      C + (K : Set G) = C + (H : Set G) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let T := C + (H : Set G)
  let K := AddAction.stabilizer G T
  have hTperiod : T + (H : Set G) = T := by dsimp only [T]; rw [add_assoc, coe_add_coe]
  have hHK : H ≤ K := subgroup_le_stabilizer_of_add_eq H T hTperiod
  have hKH : (K : Set G) + (H : Set G) = K := by
    apply subset_antisymm
    · rintro x ⟨k, hk, h, hh, rfl⟩
      exact K.add_mem hk (hHK hh)
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hKm : MeasurableSet (K : Set G) := by
    rw [← hKH]
    exact measurable_saturation_of_positive_subgroup U hU q H hHm hHpos K
  refine ⟨hKm, hHpos.trans_le (measure_mono hHK), subset_antisymm ?_ ?_⟩
  · rintro x ⟨c, hc, k, hk, rfl⟩
    have hfix : k +ᵥ T = T := hk
    change c + k ∈ T
    rw [← hfix]
    exact ⟨c, ⟨c, hc, 0, H.zero_mem, add_zero c⟩, add_comm k c⟩
  · exact add_subset_add Subset.rfl hHK

end Erdos335.Loeb

end
