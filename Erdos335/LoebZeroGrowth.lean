import Erdos335.LoebInnerSumBounds
import Erdos335.LoebMeasurableKneserIdentity
import Erdos335.LoebPeriodicEquality

/-!
# A zero-growth summand generates periods

If a positive measurable summand contains zero and adding it leaves the
other input's measure unchanged, the generated subgroup acts as a period
of the sum. The other input is periodic in measure under that subgroup.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance zeroGrowthLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_zero_growth_generated_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBne : B.Nonempty) (hzero : 0 ∈ A)
    (hinner : internalInnerMeasure U hU (A + B) = loebMeasure U hU B) :
    let H := AddSubgroup.closure A
    MeasurableSet (A + B) ∧ (A + B) + (H : Set _) = A + B ∧
      loebMeasure U hU ((B + (H : Set _)) \ B) = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let L := AddAction.stabilizer G (A + B)
  let H := AddSubgroup.closure A
  have hABlower : μ A ≤ μ B := by
    rw [← hinner]
    exact loeb_left_measure_le_sum_inner U hU A B hAm hBne
  have hBpos : 0 < μ B := hApos.trans_le hABlower
  have hsmall : internalInnerMeasure U hU (A + B) < μ A + μ B := by
    rw [hinner]
    simpa only [add_comm] using ENNReal.lt_add_right (measure_ne_top μ B) hApos.ne'
  obtain ⟨hSm, hLm, hLpos, hid⟩ := loeb_measurable_kneser_identity U hU q A B
    hAm hBm hApos hBpos hsmall
  have hSmass : μ (A + B) = μ B := (internalInnerMeasure_eq U hU _ hSm).symm.trans hinner
  have hLsub : (L : Set G) ⊆ A + (L : Set G) := fun x hx => ⟨0, hzero, x, hx, zero_add x⟩
  have hBsub : B ⊆ B + (L : Set G) := fun x hx => ⟨x, hx, 0, L.zero_mem, add_zero x⟩
  have hALbound : μ (A + (L : Set G)) ≤ μ (L : Set G) := by
    apply (ENNReal.add_le_add_iff_right (measure_ne_top μ B)).mp
    calc
      μ (A + (L : Set G)) + μ B ≤ μ (A + (L : Set G)) + μ (B + (L : Set G)) :=
        add_le_add le_rfl (measure_mono hBsub)
      _ = μ B + μ (L : Set G) := by rw [hid, hSmass]
      _ = μ (L : Set G) + μ B := add_comm _ _
  have hLperiod : (L : Set G) + (L : Set G) = L := by rw [coe_add_coe]
  have hALperiod : (A + (L : Set G)) + (L : Set G) = A + (L : Set G) := by
    rw [add_assoc, hLperiod]
  have hALeq : A + (L : Set G) = L := by
    apply loeb_periodic_sets_eq_of_ae U hU q L hLpos _ _ hALperiod hLperiod
    exact (ae_eq_of_subset_of_measure_ge hLsub hALbound hLm.nullMeasurableSet
      (measure_ne_top μ _)).symm
  have hAsubL : A ⊆ (L : Set G) := by
    intro x hx
    rw [← hALeq]
    exact ⟨x, hx, 0, L.zero_mem, add_zero x⟩
  have hHL : H ≤ L := (AddSubgroup.closure_le L).mpr hAsubL
  have hperiod : (A + B) + (H : Set G) = A + B := by
    apply subset_antisymm
    · rintro x ⟨s, hs, k, hk, rfl⟩
      have hkS : k +ᵥ (A + B) = A + B := hHL hk
      have hmem : k + s ∈ A + B := by rw [← hkS]; exact ⟨s, hs, rfl⟩
      simpa only [add_comm s k] using hmem
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hBsubS : B ⊆ A + B := fun x hx => ⟨0, hzero, x, hx, zero_add x⟩
  have hBHsubS : B + (H : Set G) ⊆ A + B := by
    intro x hx
    have hx' := add_subset_add hBsubS (show (H : Set G) ⊆ H from Subset.rfl) hx
    rwa [hperiod] at hx'
  refine ⟨hSm, hperiod, ?_⟩
  apply measure_mono_null (sdiff_subset_sdiff_left hBHsubS)
  rw [measure_sdiff hBsubS hBm.nullMeasurableSet (measure_ne_top μ _), hSmass, tsub_self]

end Erdos335.Loeb

end
