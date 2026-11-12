import Erdos335.LoebMeasurableKneserIdentity
import Erdos335.LoebCosetSums
import Erdos335.LoebConvolutionAE
import Erdos335.LoebFiniteCosetCover

/-!
# A difference-set deficit forces periodicity of the sumset

The Kneser identity gives a common saturated deficit for both signs of the
second summand. The coset filling lemma then makes the sumset periodic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance differenceDeficitLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem measurable_loeb_neg (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    Measurable (fun x : (U : Filter ℕ).Product X => -x) := by
  simpa only [zero_sub] using
    (loebMeasurePreserving_sub_left (X := X) U hU (0 : (U : Filter ℕ).Product X)).measurable

theorem loebMeasure_neg
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (hS : MeasurableSet S) :
    loebMeasure U hU (-S) = loebMeasure U hU S := by
  have hm : Measure.map (fun x : (U : Filter ℕ).Product X => -x) (loebMeasure U hU) =
      loebMeasure U hU := by
    simpa only [zero_sub] using
      (loebMeasurePreserving_sub_left (X := X) U hU (0 : (U : Filter ℕ).Product X)).map_eq
  change loebMeasure U hU ((fun x => -x) ⁻¹' S) = _
  rw [← Measure.map_apply (measurable_loeb_neg U hU) hS, hm]

theorem neg_add_subgroup {G : Type*} [AddCommGroup G] (B : Set G) (H : AddSubgroup G) :
    -(B + (H : Set G)) = (-B) + (H : Set G) := by
  ext x
  constructor
  · rintro ⟨b, hb, h, hh, heq⟩
    refine ⟨-b, ?_, -h, H.neg_mem hh, ?_⟩
    · change -(-b) ∈ B
      simpa only [neg_neg] using hb
    · change b + h = -x at heq
      calc
        -b + -h = -(b + h) := by abel
        _ = x := by rw [heq, neg_neg]
  · rintro ⟨b, hb, h, hh, heq⟩
    refine ⟨-b, hb, -h, H.neg_mem hh, ?_⟩
    change b + h = x at heq
    change -b + -h = -x
    rw [← heq]
    abel

theorem loeb_difference_deficit_periodizes_sum
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (A + (-B)) < loebMeasure U hU A + loebMeasure U hU B) :
    ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      (A + B) + (H : Set _) = A + B := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hnegBm : MeasurableSet (-B) := hBm.preimage (measurable_loeb_neg U hU)
  have hnegB : μ (-B) = μ B := loebMeasure_neg U hU B hBm
  have hnegPos : 0 < μ (-B) := by rwa [hnegB]
  have hsmall' : internalInnerMeasure U hU (A + (-B)) < μ A + μ (-B) := by rwa [hnegB]
  let H := AddAction.stabilizer G (A + (-B))
  obtain ⟨hSm, hHm, hHpos, hid⟩ := loeb_measurable_kneser_identity U hU q A (-B)
    hAm hnegBm hApos hnegPos hsmall'
  have hBSm : MeasurableSet (B + (H : Set G)) :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos B
  have hnegBS : μ ((-B) + (H : Set G)) = μ (B + (H : Set G)) := by
    rw [← neg_add_subgroup, loebMeasure_neg U hU _ hBSm]
  have hstrict : μ (A + (-B)) < μ A + μ (-B) := by
    rwa [internalInnerMeasure_eq U hU _ hSm] at hsmall'
  have hdeficit : μ (A + (H : Set G)) + μ (B + (H : Set G)) < μ A + μ B + μ (H : Set G) := by
    rw [← hnegBS, hid, ← hnegB]
    exact (ENNReal.add_lt_add_iff_right (measure_ne_top μ _)).mpr hstrict
  exact ⟨H, hHm, hHpos, loeb_add_periodic_of_saturated_deficit U hU H hHm A B hBm hdeficit⟩

end Erdos335.Loeb

end
