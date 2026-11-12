import Erdos335.LoebFiniteCosetCover

/-!
# Adding an essentially periodic Loeb summand

Finite representatives of the other input's occupied cosets reduce the
exceptional output to a finite union of translated null sets. The other
input is arbitrary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance onePeriodicSummandLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_sum_with_essentially_periodic_summand
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hBperiod : loebMeasure U hU ((B + (H : Set _)) \ B) = 0) :
    MeasurableSet (A + B) ∧ (A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  obtain ⟨R, hRA, hcover⟩ := loeb_exists_finite_coset_cover U hU q H hHm hHpos A
  let D : G → Set G := fun r => (r +ᵥ (B + (H : Set G))) \ (r +ᵥ B)
  have hD (r : G) : μ (D r) = 0 := by
    have hset : D r = (fun x => r + x) '' ((B + (H : Set G)) \ B) := by
      apply subset_antisymm
      · rintro x ⟨⟨y, hy, hxy⟩, hxout⟩
        refine ⟨y, ⟨hy, ?_⟩, hxy⟩
        intro hyB
        exact hxout ⟨y, hyB, hxy⟩
      · rintro x ⟨y, ⟨hy, hyout⟩, hxy⟩
        refine ⟨⟨y, hy, hxy⟩, ?_⟩
        rintro ⟨z, hz, hzx⟩
        have hzy : z = y := add_left_cancel (hzx.trans hxy.symm)
        exact hyout (hzy ▸ hz)
    rw [hset, loebMeasure_image_add_left]
    exact hBperiod
  have hsum : (A + B) + (H : Set G) = (R : Set G) + (B + (H : Set G)) := by
    calc
      (A + B) + (H : Set G) = (A + (H : Set G)) + B := by ac_rfl
      _ = ((R : Set G) + (H : Set G)) + B := by rw [hcover]
      _ = (R : Set G) + (B + (H : Set G)) := by ac_rfl
  have hsub : ((A + B) + (H : Set G)) \ (A + B) ⊆ ⋃ r : R, D r := by
    rintro x ⟨hx, hxout⟩
    rw [hsum] at hx
    obtain ⟨r, hr, y, hy, rfl⟩ := hx
    apply mem_iUnion.mpr
    refine ⟨⟨r, hr⟩, ⟨⟨y, hy, rfl⟩, ?_⟩⟩
    rintro ⟨b, hb, hbr⟩
    apply hxout
    exact ⟨r, hRA hr, b, hb, hbr⟩
  have hnull : μ (((A + B) + (H : Set G)) \ (A + B)) = 0 :=
    measure_mono_null hsub (measure_iUnion_null fun r : R => hD r)
  have hinside : A + B ⊆ (A + B) + (H : Set G) := by
    intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hTm : MeasurableSet ((A + B) + (H : Set G)) :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos (A + B)
  have hNm := measurable_of_loebMeasure_zero U hU _ hnull
  have hset : A + B = ((A + B) + (H : Set G)) \ (((A + B) + (H : Set G)) \ (A + B)) := by
    ext x
    constructor
    · intro hx
      exact ⟨hinside hx, fun hn => hn.2 hx⟩
    · rintro ⟨hxT, hx⟩
      by_contra hn
      exact hx ⟨hxT, hn⟩
  exact ⟨hset.symm ▸ hTm.diff hNm, (ae_le_set.mpr hnull).antisymm hinside.eventuallySubset⟩

end Erdos335.Loeb

end
