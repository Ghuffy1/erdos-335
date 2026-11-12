import Erdos335.LoebFiniteCosetCover

/-!
# Essential periodicity from full occupied cosets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance fullCosetPeriodLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_essential_period_of_full_cosets
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hfull : ∀ s ∈ S, loebMeasure U hU ((s +ᵥ (H : Set _)) \ S) = 0) :
    loebMeasure U hU ((S + (H : Set _)) \ S) = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  obtain ⟨R, hRS, hcover⟩ := loeb_exists_finite_coset_cover U hU q H hHm hHpos S
  have hsub : (S + (H : Set G)) \ S ⊆ ⋃ r : R, (((r : G) +ᵥ (H : Set G)) \ S) := by
    rintro x ⟨hx, hxout⟩
    rw [hcover] at hx
    obtain ⟨r, hr, k, hk, hkx⟩ := hx
    exact mem_iUnion.mpr ⟨⟨r, hr⟩, ⟨⟨k, hk, hkx⟩, hxout⟩⟩
  exact measure_mono_null hsub (measure_iUnion_null (fun r : R => hfull r (hRS r.property)))

end Erdos335.Loeb

end
