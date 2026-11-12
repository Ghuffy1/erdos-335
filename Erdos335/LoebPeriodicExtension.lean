import Erdos335.LoebCoarsenedPeriod
import Erdos335.LoebIrreducibleCore

/-!
# Irreducible extensions of essentially periodic cores
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance periodicExtensionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_irreducible_extension_of_periodic_core
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA'm : MeasurableSet A') (hB'm : MeasurableSet B')
    (hA'pos : 0 < loebMeasure U hU A') (hB'pos : 0 < loebMeasure U hU B')
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hAmass : loebMeasure U hU A' = loebMeasure U hU A)
    (hBmass : loebMeasure U hU B' = loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A' B')
    (hfull : internalInnerMeasure U hU (A' + B') = loebMeasure U hU A' + loebMeasure U hU B')
    (hperiod : (A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B) :
    ∃ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ∧
      ((A' + B') + (K : Set _) =ᵐ[loebMeasure U hU] A' + B' ∨
        ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A' B',
          loebMeasure U hU p.left.active = 0 ∧ loebMeasure U hU p.right.active = 0) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let K := AddAction.stabilizer G ((A + B) + (H : Set G))
  obtain ⟨hKm, hKpos, hKsum⟩ := loeb_saturation_stabilizer U hU q H hHm hHpos (A + B)
  have hCorePeriod : loebMeasure U hU (((A + B) + (K : Set G)) \ (A + B)) = 0 := by
    rw [hKsum]
    exact ae_le_set.mp hperiod.le
  have hK : K = AddAction.stabilizer G ((A + B) + (K : Set G)) := by rw [hKsum]
  refine ⟨K, hKm, hKpos, ?_⟩
  exact loeb_irreducible_periodic_core_lift U hU q K A B A' B' hKm hKpos
    hAm hBm hA'm hB'm hA'pos hB'pos hAA' hBB' hAmass hBmass hirr hfull hCorePeriod hK

end Erdos335.Loeb

end
