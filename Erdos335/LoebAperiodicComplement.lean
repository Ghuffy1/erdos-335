import Erdos335.LoebTranslationStructure

/-!
# A positive complement for a sumset with no positive essential period
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance aperiodicComplementLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_complement_pos_of_no_positive_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hno : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ S =ᵐ[loebMeasure U hU] S) :
    0 < loebMeasure U hU Sᶜ := by
  by_contra h
  have hz : loebMeasure U hU Sᶜ = 0 := le_antisymm (not_lt.mp h) bot_le
  have hS : S =ᵐ[loebMeasure U hU] univ := ae_eq_univ.mpr (mem_ae_iff.mpr hz)
  apply hno ⊤ MeasurableSet.univ (by
    change 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU univ
    rw [loebMeasure_univ]
    norm_num)
  intro t _
  have ht := loeb_vadd_congr_ae U hU S univ t hS
  rw [vadd_set_univ] at ht
  exact ht.trans hS.symm

end Erdos335.Loeb

end
