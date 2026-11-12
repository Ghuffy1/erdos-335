import Erdos335.LoebCompactEqualityReduction
import Erdos335.LoebReducibleEquality

/-!
# The remaining compact equality problem

Every positive measurable cyclic Loeb equality pair either has an exact
compact Haar equality model or has a finite-period reduction with a
null exceptional input piece. The compact inverse classification is a
separate remaining proof obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance equalityReductionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_equality_compact_or_decomposed
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B) :
    HasCompactEqualityModel U hU q A B ∨
      ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
        MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
        0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
        ((A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B ∨
          ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
            loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0) := by
  rcases loeb_irreducible_or_reducible U hU q A B with hirr | hred
  · rcases loeb_irreducible_equality_compact_or_decomposed U hU q A B hAm hBm hApos hBpos hirr hfull with hmodel | hdecomp
    · exact Or.inl hmodel
    · right
      obtain ⟨H, hHm, hHpos, hcase⟩ := hdecomp
      refine ⟨H, hHm, hHpos, ?_⟩
      rcases hcase with hperiod | ⟨p, hp, _⟩
      · exact Or.inl hperiod
      · exact Or.inr ⟨p, Or.inl hp⟩
  · obtain ⟨Acore, Bcore, hAcorem, hBcorem, hAsub, hBsub, hAmass, hBmass, hsmall⟩ := hred
    have hcore : internalInnerMeasure U hU (Acore + Bcore) <
        loebMeasure U hU Acore + loebMeasure U hU Bcore := by
      rw [hAmass, hBmass]
      exact hsmall.trans_eq hfull
    have hAcorepos : 0 < loebMeasure U hU Acore := by rwa [hAmass]
    have hBcorepos : 0 < loebMeasure U hU Bcore := by rwa [hBmass]
    obtain ⟨_, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q Acore Bcore
      hAcorem hBcorem hAcorepos hBcorepos hcore
    have hcase := loeb_reducible_equality_dichotomy U hU q Acore Bcore A B
      hAcorem hBcorem hAm hBm hAcorepos hBcorepos hAsub hBsub hAmass.symm hBmass.symm hcore hfull
    right
    exact ⟨AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (Acore + Bcore),
      hHm, hHpos, hcase⟩

end Erdos335.Loeb

end
