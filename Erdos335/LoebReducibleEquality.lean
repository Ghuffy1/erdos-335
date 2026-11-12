import Erdos335.LoebReducibleCrossStrict
import Erdos335.LoebReducibleCrossEqual

/-!
# The reducible equality case

This is the cyclic Loeb version of Griesmer's Lemma 10.9. A pair with
full input-measure equality that admits a full-measure strict critical
core has either an essential finite period or a quasi-periodic
decomposition with at least one null exceptional piece.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance reducibleEqualityLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_reducible_equality_dichotomy
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU Acore) (hBpos : 0 < loebMeasure U hU Bcore)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hAmass : loebMeasure U hU A = loebMeasure U hU Acore)
    (hBmass : loebMeasure U hU B = loebMeasure U hU Bcore)
    (hcore : internalInnerMeasure U hU (Acore + Bcore) <
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B) :
    ((A + B) + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (Acore + Bcore) : Set _) =ᵐ[loebMeasure U hU] A + B) ∨
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
        loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0 := by
  classical
  by_cases hperiod : (A + B) + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (Acore + Bcore) : Set _) =ᵐ[loebMeasure U hU] A + B
  · exact Or.inl hperiod
  right
  by_cases hleft : internalInnerMeasure U hU (A + Bcore) < loebMeasure U hU A + loebMeasure U hU Bcore
  · exact loeb_reducible_cross_strict U hU q Acore Bcore A B hAcorem hBcorem hAm hBm
      hApos hBpos hAsub hBsub hAmass hBmass hfull (Or.inl hleft) hperiod
  by_cases hright : internalInnerMeasure U hU (Acore + B) < loebMeasure U hU Acore + loebMeasure U hU B
  · exact loeb_reducible_cross_strict U hU q Acore Bcore A B hAcorem hBcorem hAm hBm
      hApos hBpos hAsub hBsub hAmass hBmass hfull (Or.inr hright) hperiod
  have hleftle : internalInnerMeasure U hU (A + Bcore) ≤ loebMeasure U hU A + loebMeasure U hU Bcore := by
    calc
      internalInnerMeasure U hU (A + Bcore) ≤ internalInnerMeasure U hU (A + B) :=
        internalInnerMeasure_mono U hU (add_subset_add Subset.rfl hBsub)
      _ = loebMeasure U hU A + loebMeasure U hU Bcore := by rw [hfull, hBmass]
  have hrightle : internalInnerMeasure U hU (Acore + B) ≤ loebMeasure U hU Acore + loebMeasure U hU B := by
    calc
      internalInnerMeasure U hU (Acore + B) ≤ internalInnerMeasure U hU (A + B) :=
        internalInnerMeasure_mono U hU (add_subset_add hAsub Subset.rfl)
      _ = loebMeasure U hU Acore + loebMeasure U hU B := by rw [hfull, hAmass]
  have hlefteq : internalInnerMeasure U hU (A + Bcore) = loebMeasure U hU Acore + loebMeasure U hU Bcore := by
    rw [← hAmass]
    exact le_antisymm hleftle (le_of_not_gt hleft)
  have hrighteq : internalInnerMeasure U hU (Acore + B) = loebMeasure U hU Acore + loebMeasure U hU Bcore := by
    rw [← hBmass]
    exact le_antisymm hrightle (le_of_not_gt hright)
  have hfulleq : internalInnerMeasure U hU (A + B) = loebMeasure U hU Acore + loebMeasure U hU Bcore := by
    rw [hfull, hAmass, hBmass]
  obtain ⟨p, hp, _⟩ := loeb_reducible_cross_equal U hU q Acore Bcore A B hAcorem hBcorem hAm hBm
    hApos hBpos hAsub hBsub hAmass hBmass hcore hlefteq hrighteq hfulleq hperiod
  exact ⟨p, Or.inl hp⟩

end Erdos335.Loeb

end
