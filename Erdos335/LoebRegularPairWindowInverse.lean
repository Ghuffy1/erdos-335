import Erdos335.LoebRegularPrefixTermination
import Erdos335.LoebTranslatedPeriods
import Erdos335.LoebRegularBohrExclusion
import Erdos335.LoebSubcriticalWindowCompensation
import Erdos335.LoebPeriodicWindowInputs
import Erdos335.LoebNullActivePeriods

/-!
# Local inverse for two inputs with zero residue-capacity gap
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance regularPairWindowInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_regular_pair_window_inverse
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
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
    (hmE : (loebMeasure U hU (internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b)
    (hsum : internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      ≤ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hgap : a + b < gamma A B)
    (happroxA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε)
    (happroxB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) B).card : ℝ) / (k : ℕ) ≤ b + ε) :
    (∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))), (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU]
          (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _)) ∨
    (∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))), (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU]
          (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _)) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let W := internalSet U D
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let C := internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  have hmW : (μ W).toReal = a :=
    (congrArg ENNReal.toReal (measure_congr hDAE)).trans hmA
  by_cases hsmall : μ (W + P) < μ W + μ P
  · obtain ⟨h, R, hd, hmask, _⟩ := subcritical_window_is_periodic U hU q hq A B start a b ha hb
      D E hDsub hDAE hEsub hexhaust hmA hmB hmC hmE hsum hsmall hgap
    exact Or.inl ⟨h, R, hd, hmask⟩
  have hSm : MeasurableSet (W + P) := by
    dsimp only [W, P]
    rw [← internalSet_add]
    exact measurable_internalSet U _
  have htotals : μ C = μ W + μ P := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (by finiteness)).mp
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hmW, hmE, hmC]
  have heq : μ (W + P) = μ C := by
    apply le_antisymm (measure_mono_ae hsum)
    rw [htotals]
    exact le_of_not_gt hsmall
  have hfull : μ (W + P) = μ W + μ P := heq.trans htotals
  have hmodelC : W + P =ᵐ[μ] C :=
    ae_eq_of_ae_subset_of_measure_ge hsum heq.symm.le hSm.nullMeasurableSet (measure_ne_top μ _)
  by_cases hperiod : ∃ H : AddSubgroup G, MeasurableSet (H : Set G) ∧ 0 < μ (H : Set G) ∧
      ∀ t ∈ H, t +ᵥ (W + P) =ᵐ[μ] W + P
  · obtain ⟨H, hHm, hHpos, hHp⟩ := hperiod
    obtain ⟨h, R, hd, hmask⟩ := loeb_ae_periods_have_natural_mask U hU q (W + P) hSm H hHm hHpos hHp
    have hCmask := hmodelC.symm.trans hmask
    obtain ⟨S, T, hS, _⟩ := periodic_output_window_forces_periodic_inputs U hU q hq h hd
      A B start a b ha hb hmA hmB hmC hgap R hCmask
    exact Or.inl ⟨h, S, hd, hS⟩
  have hnoAE : ∀ H : AddSubgroup G, MeasurableSet (H : Set G) → 0 < μ (H : Set G) →
      ¬ ∀ t ∈ H, t +ᵥ (W + P) =ᵐ[μ] W + P := by
    intro H hHm hHpos hHp
    exact hperiod ⟨H, hHm, hHpos, hHp⟩
  have hWpos : 0 < μ W := by
    apply pos_iff_ne_zero.mpr
    intro hz
    rw [hz, ENNReal.toReal_zero] at hmW
    linarith
  have hPpos : 0 < μ P := by
    apply pos_iff_ne_zero.mpr
    intro hz
    change (μ P).toReal = b at hmE
    rw [hz, ENNReal.toReal_zero] at hmE
    linarith
  have hexclude := loeb_regular_window_no_positive_terminal U hU q hdiv P W A start hDAE a hmA happroxA
  rcases loeb_regular_prefix_aperiodic_inverse U hU q hdiv hq A B start a b D E hDsub hDAE
      hEsub hexhaust hmA hmB hmE happroxB hWpos hPpos hfull hmodelC hgap hnoAE with
    hbohr | ⟨p, hterminal⟩
  · obtain ⟨b⟩ := hbohr
    exact False.elim (hexclude.1 ⟨b.swap⟩)
  · rcases hterminal with hleft | hright | hbohr
    · obtain ⟨h, R, hd, hmask⟩ := loeb_ae_periods_have_natural_mask U hU q W
        (measurable_internalSet U D) p.period p.period_measurable p.period_positive
        (loeb_quasiPeriodic_null_active_ae_periods U hU q W p.period p.left hleft)
      exact Or.inl ⟨h, R, hd, hDAE.symm.trans hmask⟩
    · right
      exact loeb_regular_prefix_periodic_window U hU q hdiv B E start hEsub hexhaust b hmE hmB
        happroxB p.period p.period_measurable p.period_positive
        (loeb_quasiPeriodic_null_active_ae_periods U hU q P p.period p.right hright)
    · obtain ⟨b⟩ := hbohr
      exact False.elim (hexclude.2 p.swap ⟨b.swap⟩)

end Erdos335.Loeb

end
