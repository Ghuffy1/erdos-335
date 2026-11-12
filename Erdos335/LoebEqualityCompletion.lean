import Erdos335.LoebEnvelopeStabilizer

/-!
# One exceptional input coset at the equality boundary

Once the cross-sum envelope has the core stabilizer, the strict Kneser
identity for a saturated input bounds its additional measure by one
coset. Positive-period rigidity turns that measure bound into equality
of literal sets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance equalityCompletionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_equality_completion_single_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (P Q A T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hPm : MeasurableSet P) (hQm : MeasurableSet Q)
    (hPpos : 0 < loebMeasure U hU P) (hQpos : 0 < loebMeasure U hU Q)
    (hPperiod : P + (H : Set _) = P) (hQperiod : Q + (H : Set _) = Q)
    (hPsub : P ⊆ A + (H : Set _)) (hA : A + Q = T) (hAout : ¬ A ⊆ P)
    (hH : AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) T = H)
    (hTmass : loebMeasure U hU T = loebMeasure U hU P + loebMeasure U hU Q) :
    ∃ a ∉ P, A + (H : Set _) = P ∪ (a +ᵥ (H : Set _)) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let R := A + (H : Set G)
  have hRm : MeasurableSet R := measurable_saturation_of_positive_subgroup U hU q H hHm hHpos A
  have hRperiod : R + (H : Set G) = R := by dsimp only [R]; rw [add_assoc, coe_add_coe]
  have hAsub : A ⊆ R := fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hRQ : R + Q = T := by
    calc
      R + Q = A + (Q + (H : Set G)) := by dsimp only [R]; ac_rfl
      _ = A + Q := by rw [hQperiod]
      _ = T := hA
  have hTperiod : T + (H : Set G) = T := by
    rw [← hA, add_assoc, hQperiod]
  have hTm : MeasurableSet T := by
    rw [← hTperiod]
    exact measurable_saturation_of_positive_subgroup U hU q H hHm hHpos T
  obtain ⟨a, ha, haout⟩ := Set.not_subset.mp hAout
  have hcosetR : a +ᵥ (H : Set G) ⊆ R := by
    rintro x ⟨k, hk, hkx⟩
    exact ⟨a, ha, k, hk, hkx⟩
  have hdisjoint : Disjoint P (a +ᵥ (H : Set G)) := by
    apply Set.disjoint_left.mpr
    rintro x hxP ⟨k, hk, hkx⟩
    have hback : x + -k ∈ P + (H : Set G) := add_mem_add hxP (H.neg_mem hk)
    rw [hPperiod] at hback
    change a + k = x at hkx
    exact haout (by simpa only [← hkx, add_neg_cancel_right] using hback)
  have hlower : μ P + μ (H : Set G) ≤ μ R := by
    rw [← loebMeasure_coset U hU H a, ← measure_union hdisjoint (measurable_loeb_coset U hU H hHm a)]
    exact measure_mono (union_subset hPsub hcosetR)
  have hinc : μ P < μ R :=
    (ENNReal.lt_add_right (measure_ne_top μ P) hHpos.ne').trans_le hlower
  have hsmall : internalInnerMeasure U hU (R + Q) < μ R + μ Q := by
    rw [hRQ, internalInnerMeasure_eq U hU T hTm, hTmass]
    exact (ENNReal.add_lt_add_iff_right (measure_ne_top μ Q)).mpr hinc
  obtain ⟨_, _, _, hidentity⟩ := loeb_measurable_kneser_identity U hU q R Q hRm hQm
    (hPpos.trans_le (measure_mono hPsub)) hQpos hsmall
  rw [hRQ, hH, hRperiod, hQperiod, hTmass] at hidentity
  have hmass : μ R = μ P + μ (H : Set G) := by
    apply (ENNReal.add_left_inj (measure_ne_top μ Q)).mp
    calc
      μ R + μ Q = (μ P + μ Q) + μ (H : Set G) := hidentity
      _ = (μ P + μ (H : Set G)) + μ Q := by ac_rfl
  exact loeb_periodic_extension_by_one_coset U hU q H hHm hHpos P R hPm hRm hPsub hPperiod hRperiod hmass

end Erdos335.Loeb

end
