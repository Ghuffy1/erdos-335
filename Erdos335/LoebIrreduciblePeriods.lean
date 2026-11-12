import Erdos335.LoebAEPeriodTransfer
import Erdos335.LoebReducibleEquality

/-!
# Reducibility forces positive translation periods

A null active part in a quasi-periodic decomposition gives translation
periods of its input. The reducible equality dichotomy therefore yields
a positive subgroup of periods for an input or for the sumset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance irreduciblePeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_null_active_ae_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H S)
    (hzero : loebMeasure U hU p.active = 0) :
    ∀ t ∈ H, t +ᵥ S =ᵐ[loebMeasure U hU] S := by
  have hBgsub : p.background ⊆ S := subset_union_left.trans p.partition.ge
  have hnull : loebMeasure U hU (S \ p.background) = 0 := by
    apply measure_mono_null _ hzero
    rintro x ⟨hx, hn⟩
    exact (p.partition ▸ hx).resolve_left hn
  have hBgAE : p.background =ᵐ[loebMeasure U hU] S :=
    hBgsub.eventuallySubset.antisymm (ae_le_set.mpr hnull)
  intro t ht
  have hfix := loeb_translate_ae_of_essential_period U hU q p.background p.background_measurable
    H p.background_periodic t ht
  exact (loeb_vadd_congr_ae U hU S p.background t hBgAE.symm).trans (hfix.trans hBgAE)

theorem loeb_irreducible_of_no_positive_ae_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hforbidden : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ((∀ t ∈ H, t +ᵥ A =ᵐ[loebMeasure U hU] A) ∨
       (∀ t ∈ H, t +ᵥ B =ᵐ[loebMeasure U hU] B) ∨
       (∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B)) → False) :
    MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B := by
  rcases loeb_irreducible_or_reducible U hU q A B with hirr | hred
  · exact hirr
  obtain ⟨P, Q, hPm, hQm, hPA, hQB, hPmass, hQmass, hsmall⟩ := hred
  have hPpos : 0 < loebMeasure U hU P := hPmass.symm ▸ hApos
  have hQpos : 0 < loebMeasure U hU Q := hQmass.symm ▸ hBpos
  have hcritical : internalInnerMeasure U hU (P + Q) < loebMeasure U hU P + loebMeasure U hU Q := by
    rw [hPmass, hQmass]
    exact hsmall.trans_eq hfull
  let H := AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (P + Q)
  obtain ⟨_, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q P Q hPm hQm hPpos hQpos hcritical
  have hcase := loeb_reducible_equality_dichotomy U hU q P Q A B hPm hQm hAm hBm
    hPpos hQpos hPA hQB hPmass.symm hQmass.symm hcritical hfull
  apply False.elim
  rcases hcase with hp | ⟨p, hz | hz⟩
  · exact hforbidden H hHm hHpos (Or.inr (Or.inr (fun t ht =>
      loeb_translate_ae_of_essential_period U hU q (A + B) hSm H (ae_le_set.mp hp.le) t ht)))
  · exact hforbidden p.period p.period_measurable p.period_positive
      (Or.inl (loeb_quasiPeriodic_null_active_ae_periods U hU q A p.period p.left hz))
  · exact hforbidden p.period p.period_measurable p.period_positive
      (Or.inr (Or.inl (loeb_quasiPeriodic_null_active_ae_periods U hU q B p.period p.right hz)))

end Erdos335.Loeb

end
