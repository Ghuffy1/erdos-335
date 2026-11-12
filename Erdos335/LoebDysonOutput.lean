import Erdos335.LoebDysonExclusiveOutput
import Erdos335.LoebDysonMixedOutput

/-!
# A quasi-periodic model of the strict Dyson output

All three coset cases give a full-measure quasi-periodic model of the
original sum at the stabilizer of the transformed sum. Recovering a
quasi-periodic decomposition of the input pair is a further step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance dysonOutputLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_strict_dyson_quasiPeriodic_output_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hIpos : 0 < loebMeasure U hU (A ∩ B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU ((A ∪ B) + (A ∩ B)) <
      loebMeasure U hU (A ∪ B) + loebMeasure U hU (A ∩ B))
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) = A + B) :
    let H := AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      ((A ∪ B) + (A ∩ B))
    ∃ D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      ∃ p : QuasiPeriodicDecomposition (loebMeasure U hU) H D,
        D ⊆ A + B ∧ (A + B =ᵐ[loebMeasure U hU] D) ∧
          p.background = (A ∪ B) + (A ∩ B) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let T := (A ∪ B) + (A ∩ B)
  let H := AddAction.stabilizer G T
  by_cases hright : ∃ a ∈ A, ∃ b ∈ B, b ∉ A + (H : Set G) ∧ a + b ∉ T
  · obtain ⟨a, ha, b, hb, hbout, hout⟩ := hright
    exact loeb_dyson_exclusive_case_quasiPeriodic_model U hU q A B hAm hBm hIpos hfull hsmall
      a b ha hb hbout hout
  by_cases hleft : ∃ b ∈ B, ∃ a ∈ A, a ∉ B + (H : Set G) ∧ a + b ∉ T
  · obtain ⟨b, hb, a, ha, haout, hout⟩ := hleft
    have hIpos' : 0 < μ (B ∩ A) := by simpa only [inter_comm B A] using hIpos
    have hfull' : μ (B + A) = μ B + μ A := by
      simpa only [add_comm B A, add_comm (μ B) (μ A)] using hfull
    have hsmall' : internalInnerMeasure U hU ((B ∪ A) + (B ∩ A)) < μ (B ∪ A) + μ (B ∩ A) := by
      simpa only [union_comm B A, inter_comm B A] using hsmall
    have hexclusive' : a ∉ B + (AddAction.stabilizer G ((B ∪ A) + (B ∩ A)) : Set G) := by
      simpa only [union_comm B A, inter_comm B A] using haout
    have hout' : b + a ∉ (B ∪ A) + (B ∩ A) := by
      simpa only [add_comm b a, union_comm B A, inter_comm B A] using hout
    have h := loeb_dyson_exclusive_case_quasiPeriodic_model U hU q B A hBm hAm hIpos' hfull'
      hsmall' b a hb ha hexclusive' hout'
    simp_rw [union_comm B A, inter_comm B A, add_comm B A] at h
    convert h using 1
    funext D
    rw [union_comm B A, inter_comm B A]
  have hleftSubset : (A \ (B + (H : Set G))) + B ⊆ T := by
    rintro z ⟨a, ha, b, hb, rfl⟩
    by_contra hout
    exact hleft ⟨b, hb, a, ha.1, ha.2, hout⟩
  have hrightSubset : A + (B \ (A + (H : Set G))) ⊆ T := by
    rintro z ⟨a, ha, b, hb, rfl⟩
    by_contra hout
    exact hright ⟨a, ha, b, hb.1, hb.2, hout⟩
  obtain ⟨p, hpT, _⟩ := loeb_dyson_mixed_case_quasiPeriodic_output U hU q A B
    hAm hBm hSm hIpos hfull hsmall hnotperiod hleftSubset hrightSubset
  exact ⟨A + B, p, Subset.rfl, Filter.EventuallyEq.rfl, hpT⟩

end Erdos335.Loeb

end
