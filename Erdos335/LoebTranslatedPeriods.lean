import Erdos335.LoebRegularPrefixWindow
import Erdos335.LoebNaturalPeriodMasks

/-!
# Transferring periods through an almost-everywhere translated model
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance translatedPeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_periods_of_translated_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (v : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hST : S =ᵐ[loebMeasure U hU] v +ᵥ T)
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hperiod : t +ᵥ S =ᵐ[loebMeasure U hU] S) :
    t +ᵥ T =ᵐ[loebMeasure U hU] T := by
  have ht := (loeb_vadd_congr_ae U hU (v +ᵥ T) S t hST.symm).trans (hperiod.trans hST)
  have hc := loeb_vadd_congr_ae U hU _ _ (-v) ht
  have heq : (-v) +ᵥ (t +ᵥ (v +ᵥ T)) = t +ᵥ T := by
    rw [vadd_vadd, vadd_vadd]
    congr 1
    abel
  rw [heq, neg_vadd_vadd] at hc
  exact hc

theorem loeb_regular_prefix_periodic_window
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (E : ℕ → Set ℕ) (start : ℕ → ℕ)
    (hEA : ∀ᶠ n in U, E n ⊆ A) (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (a : ℝ)
    (hmE : (loebMeasure U hU (internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = a)
    (hmW : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hperiod : ∀ t ∈ H, t +ᵥ internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) :
    ∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))), (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU]
          (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) := by
  have hagree := loeb_regular_prefix_window_agreement U hU q hdiv A E start hEA hexhaust a hmE hmW happrox
  apply loeb_ae_periods_have_natural_mask U hU q _ (measurable_internalSet U _) H hHm hHpos
  intro t ht
  exact loeb_periods_of_translated_ae U hU q _ _ _ hagree t (hperiod t ht)

end Erdos335.Loeb

end
