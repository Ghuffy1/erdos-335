import Erdos335.LoebNaturalPeriodMasks
import Erdos335.LoebSubcriticalWindowCompensation
import Erdos335.LoebPeriodicWindowInputs
import Erdos335.LoebLiteralModelInverse

/-!
# The literal inverse alternatives for an actual density-preserving window
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance actualWindowInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_actual_window_inverse
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (D : ∀ n, Set (ZMod (q n : ℕ))) (E : ℕ → Set ℕ)
    (hDsub : internalSet U D ⊆ internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hDAE : internalSet U D =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hEsub : ∀ᶠ n in U, E n ⊆ B) (hexhaust : ∀ v ∈ B, ∀ᶠ n in U, v ∈ E n)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hmE : (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b)
    (hsum : internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      ≤ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hgap : a + b < gamma A B)
    (hcapacity : ∀ h : ℕ+, b + δ ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) :
    let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
    let W := internalSet U D
    (∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))), (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU] (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _)) ∨
    Nonempty (InternalBohrPairData U hU q P W) ∨
    ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) P W,
      loebMeasure U hU p.left.active = 0 ∨
        Nonempty (InternalBohrPairData U hU q p.left.active p.right.active) := by
  classical
  dsimp only
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let W := internalSet U D
  let C := internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  have hmW : (μ W).toReal = a :=
    (congrArg ENNReal.toReal (measure_congr hDAE)).trans hmA
  by_cases hsmall : μ (W + P) < μ W + μ P
  · obtain ⟨h, R, hd, hmask, _⟩ := subcritical_window_is_periodic U hU q hq A B start a b ha hb
      D E hDsub hDAE hEsub hexhaust hmA hmB hmC hmE hsum hsmall hgap
    exact Or.inl ⟨h, R, hd, hmask⟩
  have hSm : MeasurableSet (P + W) := by
    dsimp only [P, W]
    rw [← internalSet_add]
    exact measurable_internalSet U _
  have hsum' : P + W ≤ᵐ[μ] C := by simpa only [add_comm] using hsum
  have htotals : μ C = μ P + μ W := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (by finiteness)).mp
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hmE, hmW, hmC]
    ring
  have heq : μ (P + W) = μ C := by
    apply le_antisymm (measure_mono_ae hsum')
    rw [htotals]
    simpa only [add_comm] using le_of_not_gt hsmall
  have hmodelC : P + W =ᵐ[μ] C :=
    ae_eq_of_ae_subset_of_measure_ge hsum' heq.symm.le hSm.nullMeasurableSet (measure_ne_top μ _)
  have hreal : (μ (P + W)).toReal ≤ b + a := by
    rw [heq, hmC]
    linarith
  rcases loeb_literal_model_inverse U hU q B E D hEsub hexhaust b a δ hb ha hδ hmE hmW hcapacity hreal with
    ⟨H, hHm, hHpos, hperiod⟩ | hbohr | ⟨p, hterminal⟩
  · obtain ⟨h, R, hd, hmask⟩ := loeb_ae_periods_have_natural_mask U hU q (P + W) hSm H hHm hHpos hperiod
    have hCmask := hmodelC.symm.trans hmask
    obtain ⟨S, T, hS, hT⟩ := periodic_output_window_forces_periodic_inputs U hU q hq h hd
      A B start a b ha hb hmA hmB hmC hgap R hCmask
    exact Or.inl ⟨h, S, hd, hS⟩
  · exact Or.inr (Or.inl hbohr)
  · rcases hterminal with hleft | hright | hbohr
    · exact Or.inr (Or.inr ⟨p, Or.inl hleft⟩)
    · obtain ⟨h, R, hd, hmask⟩ := loeb_ae_periods_have_natural_mask U hU q W
        (measurable_internalSet U D) p.period p.period_measurable p.period_positive
        (loeb_quasiPeriodic_null_active_ae_periods U hU q W p.period p.right hright)
      exact Or.inl ⟨h, R, hd, hDAE.symm.trans hmask⟩
    · exact Or.inr (Or.inr ⟨p, Or.inr hbohr⟩)

end Erdos335.Loeb

end
