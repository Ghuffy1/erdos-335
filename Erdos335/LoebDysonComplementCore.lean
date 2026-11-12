import Erdos335.LoebGeneralDysonOutput
import Erdos335.LoebQuasiPeriodicActiveBounds
import Erdos335.LoebQuasiPeriodicComplement
import Erdos335.LoebEnvelopeStabilizer

/-!
# A quasi-periodic complement core from a strict Dyson transform
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance dysonComplementCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_strict_dyson_complement_core
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (e : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hIpos : 0 < loebMeasure U hU (dysonGroupRight A B e))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (dysonGroupLeft A B e + dysonGroupRight A B e) <
      loebMeasure U hU A + loebMeasure U hU B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      ∃ C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
        C ⊆ (A + B)ᶜ ∧ C =ᵐ[loebMeasure U hU] (A + B)ᶜ ∧
        ∃ r : QuasiPeriodicDecomposition (loebMeasure U hU) H C,
          0 < loebMeasure U hU r.active := by
  have hnotexact : ¬ ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      (A + B) + (H : Set _) = A + B := by
    rintro ⟨H, hHm, hHpos, hp⟩
    apply hnoAE H hHm hHpos
    intro t ht
    have hfix : t +ᵥ (A + B) = A + B := subgroup_le_stabilizer_of_add_eq H (A + B) hp ht
    rw [hfix]
  obtain ⟨H, hHm, hHpos, D, ⟨p⟩, _, hSD⟩ := loeb_general_strict_dyson_output_model U hU q
    A B hAm hBm hSm e hIpos hfull hsmall hnotexact
  have hpartial := (loeb_quasiPeriodic_active_mass_bounds U hU q (A + B) D H p
    hSD.symm (hnoAE H hHm hHpos)).2
  obtain ⟨C, hCS, hCae, r, hrpos⟩ := loeb_quasiPeriodic_complement_core U hU q (A + B) D hSm H
    hHm hHpos p hSD.symm hpartial
  exact ⟨H, hHm, hHpos, C, hCS, hCae, r, hrpos⟩

end Erdos335.Loeb

end
