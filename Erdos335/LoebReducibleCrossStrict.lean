import Erdos335.LoebQuasiPeriodicData

/-!
# Reducible equality pairs with a strict cross sum

Null deletion on one side identifies the strict cross sum with the
critical core. The one-sided reduction then supplies a quasi-periodic
decomposition. This is the first case of Griesmer's Lemma 10.9.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance reducibleCrossLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_reducible_left_cross_strict
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU Acore) (hBpos : 0 < loebMeasure U hU Bcore)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hAmass : loebMeasure U hU A = loebMeasure U hU Acore)
    (hBmass : loebMeasure U hU B = loebMeasure U hU Bcore)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hcross : internalInnerMeasure U hU (A + Bcore) < loebMeasure U hU A + loebMeasure U hU Bcore)
    (hnotperiod : ¬ (A + B) + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (Acore + Bcore) : Set _) =ᵐ[loebMeasure U hU] A + B) :
    ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      loebMeasure U hU p.right.active = 0 := by
  have hsum : A + Bcore = Acore + Bcore :=
    loeb_critical_null_extensions_sum_eq U hU q Acore Bcore A Bcore
      hAcorem hBcorem hApos hBpos hAsub Subset.rfl hAmass rfl hcross
  have hpositive : 0 < loebMeasure U hU A := by rwa [hAmass]
  have hequality' : internalInnerMeasure U hU (A + B) =
      loebMeasure U hU A + loebMeasure U hU Bcore := by rwa [hBmass] at hequality
  apply exists_quasiPeriodicPairData_of_one_sided_equality U hU q A Bcore B
    hAm hBcorem hBm hpositive hBpos hBsub hBmass hcross hequality'
  rwa [hsum]

theorem loeb_reducible_cross_strict
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU Acore) (hBpos : 0 < loebMeasure U hU Bcore)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hAmass : loebMeasure U hU A = loebMeasure U hU Acore)
    (hBmass : loebMeasure U hU B = loebMeasure U hU Bcore)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hcross : internalInnerMeasure U hU (A + Bcore) < loebMeasure U hU A + loebMeasure U hU Bcore ∨
      internalInnerMeasure U hU (Acore + B) < loebMeasure U hU Acore + loebMeasure U hU B)
    (hnotperiod : ¬ (A + B) + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (Acore + Bcore) : Set _) =ᵐ[loebMeasure U hU] A + B) :
    ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0 := by
  rcases hcross with hleft | hright
  · obtain ⟨p, hp⟩ := loeb_reducible_left_cross_strict U hU q Acore Bcore A B
      hAcorem hBcorem hAm hBm hApos hBpos hAsub hBsub hAmass hBmass hequality hleft hnotperiod
    exact ⟨p, Or.inr hp⟩
  · have hequality' : internalInnerMeasure U hU (B + A) =
        loebMeasure U hU B + loebMeasure U hU A := by simpa only [add_comm] using hequality
    have hright' : internalInnerMeasure U hU (B + Acore) <
        loebMeasure U hU B + loebMeasure U hU Acore := by simpa only [add_comm] using hright
    have hnotperiod' : ¬ (B + A) + (AddAction.stabilizer
        ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (Bcore + Acore) : Set _) =ᵐ[loebMeasure U hU] B + A := by
      simpa only [add_comm] using hnotperiod
    obtain ⟨p, hp⟩ := loeb_reducible_left_cross_strict U hU q Bcore Acore B A
      hBcorem hAcorem hBm hAm hBpos hApos hBsub hAsub hBmass hAmass hequality' hright' hnotperiod'
    exact ⟨p.swap, Or.inl hp⟩

end Erdos335.Loeb

end
