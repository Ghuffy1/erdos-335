import Erdos335.LoebIrreducibleInverse
import Erdos335.LoebEqualityReduction

/-!
# The aperiodic Loeb equality inverse theorem
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance aperiodicInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_aperiodic_equality_quasiPeriodic_or_internalBohr
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) ∨
      Nonempty (InternalBohrPairData U hU q A B) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hinner : internalInnerMeasure U hU (A + B) = μ A + μ B :=
    (internalInnerMeasure_eq U hU _ hSm).trans hfull
  have hne : MeasureNonextendible μ (internalInnerMeasure U hU) A B := by
    apply loeb_nonextendible_of_no_essential_period U hU q A B hAm hBm hApos hBpos hinner
    intro h hperiod
    apply hnoAE (naturalCyclicKernel U q h) (measurable_naturalCyclicKernel U q h)
      (naturalCyclicKernel_measure_pos U hU q h)
    intro t ht
    exact loeb_translate_ae_of_essential_period U hU q (A + B) hSm (naturalCyclicKernel U q h)
      (ae_le_set.mp hperiod.le) t ht
  rcases loeb_irreducible_or_reducible U hU q A B with hirr | hred
  · exact loeb_irreducible_aperiodic_quasiPeriodic_or_internalBohr U hU q A B
      hAm hBm hSm hApos hBpos hfull hirr hne hnoAE
  · obtain ⟨Acore, Bcore, hAcorem, hBcorem, hAsub, hBsub, hAmass, hBmass, hsmall⟩ := hred
    have hcore : internalInnerMeasure U hU (Acore + Bcore) < μ Acore + μ Bcore := by
      rw [hAmass, hBmass]
      exact hsmall.trans_eq hinner
    have hAcorepos : 0 < μ Acore := by rwa [hAmass]
    have hBcorepos : 0 < μ Bcore := by rwa [hBmass]
    obtain ⟨_, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q Acore Bcore
      hAcorem hBcorem hAcorepos hBcorepos hcore
    rcases loeb_reducible_equality_dichotomy U hU q Acore Bcore A B
      hAcorem hBcorem hAm hBm hAcorepos hBcorepos hAsub hBsub
      hAmass.symm hBmass.symm hcore hinner with hperiod | ⟨p, _⟩
    · exfalso
      let H := AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (Acore + Bcore)
      apply hnoAE H hHm hHpos
      intro t ht
      exact loeb_translate_ae_of_essential_period U hU q (A + B) hSm H
        (ae_le_set.mp hperiod.le) t ht
    · exact Or.inl ⟨p⟩

end Erdos335.Loeb

end
