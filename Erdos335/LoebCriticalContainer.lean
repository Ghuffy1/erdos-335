import Erdos335.LoebIrreducibleCore

/-!
# Irreducible equality pairs inside a strict critical container

An almost-everywhere input containment and a sumset inner-measure bound
allow the strict measurable Kneser theorem to supply a periodic core.
The core-lifting result then handles the original pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance criticalContainerLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_irreducible_pair_in_critical_container
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B P Q : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hPm : MeasurableSet P) (hQm : MeasurableSet Q)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hAP : A ≤ᵐ[loebMeasure U hU] P) (hBQ : B ≤ᵐ[loebMeasure U hU] Q)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hbound : internalInnerMeasure U hU (P + Q) ≤ internalInnerMeasure U hU (A + B))
    (hsmall : internalInnerMeasure U hU (P + Q) < loebMeasure U hU P + loebMeasure U hU Q) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (P + Q)
    MeasurableSet (H : Set G) ∧ 0 < loebMeasure U hU (H : Set G) ∧
      ((A + B) + (H : Set G) =ᵐ[loebMeasure U hU] A + B ∨
        ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
          loebMeasure U hU p.left.active = 0 ∧ loebMeasure U hU p.right.active = 0) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let H := AddAction.stabilizer G (P + Q)
  obtain ⟨hTm, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q P Q hPm hQm
    (hApos.trans_le (measure_mono_ae hAP)) (hBpos.trans_le (measure_mono_ae hBQ)) hsmall
  let Acore := A ∩ P
  let Bcore := B ∩ Q
  have hAmass : μ Acore = μ A := by
    apply measure_congr
    filter_upwards [hAP] with x hx
    change x ∈ A → x ∈ P at hx
    change (x ∈ A ∧ x ∈ P) = (x ∈ A)
    apply propext
    tauto
  have hBmass : μ Bcore = μ B := by
    apply measure_congr
    filter_upwards [hBQ] with x hx
    change x ∈ B → x ∈ Q at hx
    change (x ∈ B ∧ x ∈ Q) = (x ∈ B)
    apply propext
    tauto
  have hCoreEq : internalInnerMeasure U hU (Acore + Bcore) = internalInnerMeasure U hU (A + B) :=
    hirr Acore Bcore (hAm.inter hPm) (hBm.inter hQm) inter_subset_left inter_subset_left hAmass hBmass
  have hCoreSub : Acore + Bcore ⊆ P + Q := add_subset_add inter_subset_right inter_subset_right
  have hTeq : internalInnerMeasure U hU (P + Q) = internalInnerMeasure U hU (A + B) := by
    apply le_antisymm hbound
    rw [← hCoreEq]
    exact internalInnerMeasure_mono U hU hCoreSub
  have hCoreFull : internalInnerMeasure U hU (Acore + Bcore) = μ (P + Q) :=
    hCoreEq.trans (hTeq.symm.trans (internalInnerMeasure_eq U hU (P + Q) hTm))
  obtain ⟨_, hCoreAE⟩ := measurable_of_subset_full_inner U hU (Acore + Bcore) (P + Q) hCoreSub hTm hCoreFull
  have hTperiod : (P + Q) + (H : Set G) = P + Q := by
    apply subset_antisymm
    · rintro x ⟨y, hy, k, hk, rfl⟩
      have hfix : k +ᵥ (P + Q) = P + Q := hk
      rw [← hfix]
      exact ⟨y, hy, add_comm k y⟩
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hCorePeriod := loeb_essential_period_of_full_inner_subset U hU q H
    (Acore + Bcore) (P + Q) hCoreSub hCoreFull hTperiod
  have hSatPeriod : ((Acore + Bcore) + (H : Set G)) + (H : Set G) =
      (Acore + Bcore) + (H : Set G) := by rw [add_assoc, coe_add_coe]
  have hSatEq : (Acore + Bcore) + (H : Set G) = P + Q :=
    loeb_periodic_sets_eq_of_ae U hU q H hHpos _ _ hSatPeriod hTperiod (hCorePeriod.trans hCoreAE)
  have hHcore : H = AddAction.stabilizer G ((Acore + Bcore) + (H : Set G)) := by rw [hSatEq]
  refine ⟨hHm, hHpos, ?_⟩
  exact loeb_irreducible_periodic_core_lift U hU q H Acore Bcore A B hHm hHpos
    (hAm.inter hPm) (hBm.inter hQm) hAm hBm hApos hBpos inter_subset_left inter_subset_left
    hAmass.symm hBmass.symm hirr hfull (ae_le_set.mp hCorePeriod.le) hHcore

end Erdos335.Loeb

end
