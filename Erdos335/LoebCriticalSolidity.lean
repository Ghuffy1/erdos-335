import Erdos335.LoebCosetSums
import Erdos335.LoebMeasurableKneserIdentity

/-!
# Positive sections of strict critical pairs

The saturated Kneser identity bounds every occupied coset section from
below by the total deficit. This is the solidity assertion in Griesmer's
Lemma 9.6 for measurable summands in cyclic Loeb groups.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance solidityLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_coset_section_bound_of_kneser_identity
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (A B : Set ((U : Filter ℕ).Product X))
    (heq : loebMeasure U hU (A + (H : Set ((U : Filter ℕ).Product X))) +
        loebMeasure U hU (B + (H : Set ((U : Filter ℕ).Product X))) =
      loebMeasure U hU (A + B) + loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)))
    (a : (U : Filter ℕ).Product X) (ha : a ∈ A) :
    loebMeasure U hU A + loebMeasure U hU B ≤ loebMeasure U hU (A + B) +
      loebMeasure U hU (A ∩ (a +ᵥ (H : Set ((U : Filter ℕ).Product X)))) := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hA := loeb_coset_section_measure_le U hU H hH A a ha
  have hB : μ B ≤ μ (B + (H : Set G)) := by
    apply measure_mono
    intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hbound : (μ A + μ B) + μ (H : Set G) ≤
      (μ (A + B) + μ (A ∩ (a +ᵥ (H : Set G)))) + μ (H : Set G) := by
    calc
      (μ A + μ B) + μ (H : Set G) = (μ A + μ (H : Set G)) + μ B := by ac_rfl
      _ ≤ (μ (A + (H : Set G)) + μ (A ∩ (a +ᵥ (H : Set G)))) +
          μ (B + (H : Set G)) := add_le_add hA hB
      _ = (μ (A + (H : Set G)) + μ (B + (H : Set G))) +
          μ (A ∩ (a +ᵥ (H : Set G))) := by ac_rfl
      _ = (μ (A + B) + μ (H : Set G)) + μ (A ∩ (a +ᵥ (H : Set G))) := by rw [heq]
      _ = (μ (A + B) + μ (A ∩ (a +ᵥ (H : Set G)))) + μ (H : Set G) := by ac_rfl
  exact (ENNReal.add_le_add_iff_right (measure_ne_top μ _)).mp hbound

theorem loeb_coset_section_positive_of_kneser_identity
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (A B : Set ((U : Filter ℕ).Product X))
    (heq : loebMeasure U hU (A + (H : Set ((U : Filter ℕ).Product X))) +
        loebMeasure U hU (B + (H : Set ((U : Filter ℕ).Product X))) =
      loebMeasure U hU (A + B) + loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)))
    (hsmall : loebMeasure U hU (A + B) < loebMeasure U hU A + loebMeasure U hU B)
    (a : (U : Filter ℕ).Product X) (ha : a ∈ A) :
    0 < loebMeasure U hU (A ∩ (a +ᵥ (H : Set ((U : Filter ℕ).Product X)))) := by
  have hbound := loeb_coset_section_bound_of_kneser_identity U hU H hH A B heq a ha
  by_contra hn
  have hz : loebMeasure U hU (A ∩ (a +ᵥ (H : Set ((U : Filter ℕ).Product X)))) = 0 :=
    le_antisymm (not_lt.mp hn) zero_le
  rw [hz, add_zero] at hbound
  exact (not_lt_of_ge hbound) hsmall

theorem loeb_critical_coset_masses_positive
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (A + B) < loebMeasure U hU A + loebMeasure U hU B) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + B)
    (∀ a ∈ A, 0 < loebMeasure U hU (A ∩ (a +ᵥ (H : Set G)))) ∧
      (∀ b ∈ B, 0 < loebMeasure U hU (B ∩ (b +ᵥ (H : Set G)))) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let H := AddAction.stabilizer G (A + B)
  obtain ⟨hC, hH, _, heq⟩ := loeb_measurable_kneser_identity U hU q A B hA hB hApos hBpos hsmall
  have hlt : μ (A + B) < μ A + μ B := by
    rwa [internalInnerMeasure_eq U hU (A + B) hC] at hsmall
  have heq' : μ (B + (H : Set G)) + μ (A + (H : Set G)) = μ (B + A) + μ (H : Set G) := by
    rw [add_comm B A, add_comm (μ (B + (H : Set G))) (μ (A + (H : Set G)))]
    exact heq
  constructor
  · intro a ha
    exact loeb_coset_section_positive_of_kneser_identity U hU H hH A B heq hlt a ha
  · intro b hb
    apply loeb_coset_section_positive_of_kneser_identity U hU H hH B A heq' _ b hb
    simpa only [add_comm] using hlt

end Erdos335.Loeb

end
