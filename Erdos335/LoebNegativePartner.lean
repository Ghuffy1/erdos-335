import Erdos335.LoebQuasiPeriodicPartner
import Erdos335.LoebQuasiPeriodicNeg

/-!
# Recovering the original pair from a negated partner
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance negativePartnerLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_pair_of_negative_full_measure_partner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B Q : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H Q)
    (hQB : Q ⊆ -B) (hQmass : loebMeasure U hU Q = loebMeasure U hU (-B))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hlarge : loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) < loebMeasure U hU (A + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) →
      ¬ ∀ t ∈ K, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  have hQm : MeasurableSet Q := p.partition.symm ▸ (p.background_measurable.union p.active_measurable)
  have hnegQB : -Q ⊆ B := by
    intro x hx
    have h : -x ∈ -B := hQB hx
    simpa only [Set.mem_neg, neg_neg] using h
  have hnegQmass : loebMeasure U hU (-Q) = loebMeasure U hU B := by
    rw [loebMeasure_neg U hU Q hQm, hQmass, loebMeasure_neg U hU B hBm]
  exact loeb_quasiPeriodic_pair_of_full_measure_partner U hU q A B (-Q) H hHm hHpos
    (p.loebNeg U hU) hnegQB hnegQmass hAm hBm hSm hApos hBpos hlarge hfull hirr hnoAE

theorem loeb_pair_of_negative_positive_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H (-B))
    (hBgpos : 0 < loebMeasure U hU p.background)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) →
      ¬ ∀ t ∈ K, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  have hmodel : ∃ r : QuasiPeriodicDecomposition (loebMeasure U hU) H B,
      0 < loebMeasure U hU r.background := by
    have hpos : 0 < loebMeasure U hU (p.loebNeg U hU).background := by
      change 0 < loebMeasure U hU (-p.background)
      rwa [loebMeasure_neg U hU p.background p.background_measurable]
    have hmodel' : ∃ r : QuasiPeriodicDecomposition (loebMeasure U hU) H (-(-B)),
        0 < loebMeasure U hU r.background := ⟨p.loebNeg U hU, hpos⟩
    have hBB : -(-B) = B := by
      ext x
      simp only [Set.mem_neg, neg_neg]
    rw [hBB] at hmodel'
    exact hmodel'
  obtain ⟨r, hrpos⟩ := hmodel
  have hBAno : ¬ ∃ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ∧
      (B + A) + (K : Set _) =ᵐ[loebMeasure U hU] B + A := by
    rintro ⟨K, hKm, hKpos, hp⟩
    apply hnoAE K hKm hKpos
    intro t ht
    have h := loeb_translate_ae_of_essential_period U hU q (B + A)
      (by simpa only [add_comm B A] using hSm) K (ae_le_set.mp hp.le) t ht
    simpa only [add_comm B A] using h
  obtain ⟨s⟩ := loeb_quasiPeriodic_pair_of_nonnull_background U hU q B A H hHm hHpos r
    hAm (by simpa only [add_comm B A] using hSm) hrpos hBpos hApos
    (by simpa only [add_comm] using hfull) hirr.swap hne.swap hBAno
  exact ⟨s.swap⟩

end Erdos335.Loeb

end
