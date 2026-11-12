import Erdos335.LoebDifferenceDeficit
import Erdos335.LoebNonextendible
import Erdos335.LoebFullInner

/-!
# Complement duality for a nonextendible equality pair

For C equal to the complement of A+B, the pair -B,C has sum equal almost
everywhere to the complement of A. A strict deficit would produce a
measurable enlargement of A with the same literal sumset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance complementDualityLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_nonextendible_complement_duality
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hBpos : 0 < loebMeasure U hU B)
    (hCpos : 0 < loebMeasure U hU (A + B)ᶜ)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B) :
    MeasurableSet ((-B) + (A + B)ᶜ) ∧
      (-B) + (A + B)ᶜ =ᵐ[loebMeasure U hU] Aᶜ ∧
      internalInnerMeasure U hU ((-B) + (A + B)ᶜ) =
        loebMeasure U hU (-B) + loebMeasure U hU (A + B)ᶜ := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let C := (A + B)ᶜ
  let E := (-B) + C
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hnegBm : MeasurableSet (-B) := hBm.preimage (measurable_loeb_neg U hU)
  have hnegB : μ (-B) = μ B := loebMeasure_neg U hU B hBm
  have hdual : μ (-B) + μ C = μ Aᶜ := by
    have hleft : (μ (-B) + μ C) + μ A = 1 := by
      rw [hnegB]
      calc
        (μ B + μ C) + μ A = (μ A + μ B) + μ C := by ac_rfl
        _ = μ (A + B) + μ (A + B)ᶜ := by rw [← hfull]
        _ = 1 := by rw [measure_add_measure_compl hSm, measure_univ]
    have hright : μ Aᶜ + μ A = 1 := by
      rw [add_comm, measure_add_measure_compl hAm, measure_univ]
    exact (ENNReal.add_left_inj (measure_ne_top μ A)).mp (hleft.trans hright.symm)
  have hEsub : E ⊆ Aᶜ := by
    rintro x ⟨nb, hnb, c, hc, rfl⟩ hx
    exact hc ⟨nb + c, hx, -nb, hnb, by abel⟩
  have hupper : internalInnerMeasure U hU E ≤ μ Aᶜ :=
    (internalInnerMeasure_le U hU E).trans (measure_mono hEsub)
  have hinner : internalInnerMeasure U hU E = μ Aᶜ := by
    apply le_antisymm hupper
    by_contra h
    have hstrict : internalInnerMeasure U hU E < μ Aᶜ := lt_of_not_ge h
    have hsmall : internalInnerMeasure U hU ((-B) + C) < μ (-B) + μ C := by
      rw [hdual]
      exact hstrict
    have hnegBpos : 0 < μ (-B) := by rwa [hnegB]
    obtain ⟨hEm, _, _, _⟩ := loeb_measurable_kneser_identity U hU q (-B) C hnegBm hSm.compl
      hnegBpos hCpos hsmall
    have hAA' : A ⊆ Eᶜ := by
      intro x hxA hxE
      exact hEsub hxE hxA
    have hsum : Eᶜ + B = A + B := by
      apply subset_antisymm
      · rintro z ⟨a, ha, b, hb, rfl⟩
        by_contra hz
        apply ha
        exact ⟨-b, by change -(-b) ∈ B; simpa only [neg_neg] using hb,
          a + b, hz, by abel⟩
      · exact add_subset_add hAA' Subset.rfl
    have hmass : μ Eᶜ = μ A := loeb_nonextendible_left_extension_eq U hU A B Eᶜ
      hBm hEm.compl hAA' hne (by rw [hsum])
    have hEmeasure : μ E = μ Aᶜ := by
      calc
        μ E = μ Eᶜᶜ := by rw [compl_compl]
        _ = 1 - μ Eᶜ := by rw [measure_compl hEm.compl (measure_ne_top μ Eᶜ), measure_univ]
        _ = 1 - μ A := by rw [hmass]
        _ = μ Aᶜ := by rw [measure_compl hAm (measure_ne_top μ A), measure_univ]
    rw [internalInnerMeasure_eq U hU E hEm, hEmeasure] at hstrict
    exact (lt_irrefl _) hstrict
  obtain ⟨hEm, hEae⟩ := measurable_of_subset_full_inner U hU E Aᶜ hEsub hAm.compl hinner
  exact ⟨hEm, hEae, hinner.trans hdual.symm⟩

end Erdos335.Loeb

end
