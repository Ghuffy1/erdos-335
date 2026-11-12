import Erdos335.LoebQuasiPeriodicLifting
import Erdos335.LoebExtendible
import Erdos335.CompactDysonTransform

/-!
# Essential periods of a nonextendible pair

An essential translation period of the sum is an essential translation
period of each input. Conversely, the absence of an essential finite
period forces an equality pair to be nonextendible.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance nonextendiblePeriodsLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_nonextendible_left_ae_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (t : (U : Filter ℕ).Product X)
    (hperiod : t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    t +ᵥ A =ᵐ[loebMeasure U hU] A := by
  let μ := loebMeasure (X := X) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let A' := A ∪ (t +ᵥ A)
  have htAm : MeasurableSet (t +ᵥ A) := by
    rw [vadd_set_eq_neg_preimage]
    exact hAm.preimage (measurable_add_left U hU (-t))
  have hA'm : MeasurableSet A' := hAm.union htAm
  have htranslate : (t +ᵥ A) + B = t +ᵥ (A + B) := by
    ext z
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, b, hb, rfl⟩
      exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by simp only [vadd_eq_add]; abel⟩
    · rintro ⟨s, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨t + a, ⟨a, ha, rfl⟩, b, hb, by simp only [vadd_eq_add]; abel⟩
  have hsum : A' + B =ᵐ[μ] A + B := by
    change (A ∪ (t +ᵥ A)) + B =ᵐ[μ] A + B
    rw [union_add, htranslate]
    filter_upwards [hperiod] with x hx
    change (x ∈ A + B ∨ x ∈ t +ᵥ (A + B)) = (x ∈ A + B)
    rw [hx]
    exact or_self _
  have hmass : μ A' = μ A := loeb_nonextendible_left_extension_eq U hU A B A'
    hBm hA'm subset_union_left hne (internalInnerMeasure_congr_ae U hU _ _ hsum)
  have htMass : μ (t +ᵥ A) = μ A := loebMeasure_image_add_left U hU t A
  have hleft : A =ᵐ[μ] A' := ae_eq_of_subset_of_measure_ge subset_union_left hmass.le
    hAm.nullMeasurableSet (measure_ne_top μ A')
  have hright : t +ᵥ A =ᵐ[μ] A' := ae_eq_of_subset_of_measure_ge subset_union_right
    (hmass.trans htMass.symm).le htAm.nullMeasurableSet (measure_ne_top μ A')
  exact hright.trans hleft.symm

theorem loeb_nonextendible_inputs_ae_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (t : (U : Filter ℕ).Product X)
    (hperiod : t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    (t +ᵥ A =ᵐ[loebMeasure U hU] A) ∧ (t +ᵥ B =ᵐ[loebMeasure U hU] B) := by
  refine ⟨loeb_nonextendible_left_ae_period U hU A B hAm hBm hne t hperiod, ?_⟩
  apply loeb_nonextendible_left_ae_period U hU B A hBm hAm hne.swap t
  simpa only [add_comm B A] using hperiod

theorem loeb_nonextendible_of_no_essential_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hperiod : ∀ h : ℕ+,
      ¬ (A + B) + (naturalCyclicKernel U q h : Set _) =ᵐ[loebMeasure U hU] A + B) :
    MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B := by
  classical
  by_contra hne
  unfold MeasureNonextendible at hne
  push Not at hne
  obtain ⟨A', B', hA'm, hB'm, hAA', hBB', hsame, hlarge⟩ := hne
  obtain ⟨_, h, hh⟩ := extendible_inner_equality_pair_has_essential_period U hU q A B A' B'
    hAm hBm hA'm hB'm hAA' hBB' hApos hBpos hfull hlarge hsame
  exact hperiod h hh

end Erdos335.Loeb

end
