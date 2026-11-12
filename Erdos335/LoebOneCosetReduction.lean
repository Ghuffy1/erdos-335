import Erdos335.LoebGeneratedSubgroup
import Erdos335.LoebOneCosetInput
import Erdos335.LoebTranslationStructure
import Erdos335.LoebNullExtensionBackground

/-!
# Reduction from an input contained in one coset

Centering the first input gives a positive measurable generated subgroup
inside the specified period. The one-coset argument gives a quasi-periodic
decomposition of the second input with this smaller period.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance oneCosetReductionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_one_coset_input_reduction
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hAcoset : A ⊆ a +ᵥ (H : Set _))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) = A + B) :
    ∃ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ∧ K ≤ H ∧
      Nonempty (QuasiPeriodicDecomposition (loebMeasure U hU) K B) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hApos.ne'
  let C := (-x) +ᵥ A
  let K := AddSubgroup.closure C
  have hCm : MeasurableSet C := measurable_loeb_translate U hU A hAm (-x)
  have hCmass : μ C = μ A := loebMeasure_image_add_left U hU (-x) A
  have hCpos : 0 < μ C := hCmass.symm ▸ hApos
  have hzero : (0 : G) ∈ C := ⟨x, hx, neg_add_cancel x⟩
  obtain ⟨hKm, hKpos⟩ := measurable_loeb_generated_subgroup U hU q C hCm hCpos
  have hKH : K ≤ H := by
    apply (AddSubgroup.closure_le H).mpr
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨kx, hkx, hkxx⟩ := hAcoset hx
    obtain ⟨ky, hky, hkyy⟩ := hAcoset hy
    have heq : -x + y = ky - kx := by
      change a + kx = x at hkxx
      change a + ky = y at hkyy
      rw [← hkxx, ← hkyy]
      abel
    change -x + y ∈ H
    rw [heq]
    exact H.sub_mem hky hkx
  have hsum : C + B = (-x) +ᵥ (A + B) := vadd_set_add_eq (-x) A B
  have hCBm : MeasurableSet (C + B) := hsum ▸ measurable_loeb_translate U hU (A + B) hSm (-x)
  have hCBmass : μ (C + B) = μ C + μ B := by
    rw [hsum, show μ ((-x) +ᵥ (A + B)) = μ (A + B) from loebMeasure_image_add_left U hU (-x) _,
      hfull, hCmass]
  have hCBnotperiod : ¬ ∃ L : AddSubgroup G, MeasurableSet (L : Set G) ∧
      0 < μ (L : Set G) ∧ (C + B) + (L : Set G) = C + B := by
    rintro ⟨L, hLm, hLpos, hperiod⟩
    apply hnotperiod
    refine ⟨L, hLm, hLpos, ?_⟩
    rw [hsum, vadd_set_add_eq] at hperiod
    have h := congrArg (fun S : Set G => x +ᵥ S) hperiod
    simpa only [vadd_vadd, add_neg_cancel, zero_vadd] using h
  refine ⟨K, hKm, hKpos, hKH, ?_⟩
  exact loeb_one_generated_coset_input_quasiPeriodic U hU q C B K hKm hKpos rfl
    hCm hBm hCBm hCpos hzero hCBmass hCBnotperiod

end Erdos335.Loeb

end
