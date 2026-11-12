import Erdos335.LoebCyclicModelConstruction
import Erdos335.LoebNaturalPeriodMasks
import Erdos335.LoebIrreduciblePeriods
import Erdos335.LoebPeriodicWindowInputs

/-!
# Actual zero-start prefixes and null-prefix indicator profiles

Privately checked supporting development.
The finite-prefix agreement retains the actual zero-window containment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance prefixAgreementLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

private theorem zero_window_counts_tendsto
    (q : ℕ → ℕ+) (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A : Set ℕ) (a : ℝ) (hA : HasDensity A a) :
    Tendsto (fun n => ((cyclicWindow A 0 (q n : ℕ)).card : ℝ) / (q n : ℕ))
      atTop (𝓝 a) := by
  have hprefix := ((hasDensity_iff_prefixCount A a).mp hA).comp hq
  have hzero : tailShift A 0 = A := by
    ext n
    simp [tailShift]
  simpa only [Function.comp_def, cyclicWindow_card_eq_prefixCount, hzero] using hprefix

theorem loeb_zero_window_mass_of_density
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A : Set ℕ) (a : ℝ) (hA : HasDensity A a) :
    (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a := by
  exact loeb_finset_measure_eq U hU q (fun n => cyclicWindow A 0 (q n : ℕ)) a
    (zero_window_counts_tendsto q hq A a hA)

theorem loeb_finite_prefix_agreement
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A : Set ℕ) (a : ℝ) (hA : HasDensity A a)
    (F : ∀ n, Finset (ZMod (q n : ℕ)))
    (hFsub : ∀ n, F n ⊆ cyclicWindow A 0 (q n : ℕ))
    (hFmass : Tendsto (fun n => ((F n).card : ℝ) / (q n : ℕ)) atTop (𝓝 a)) :
    internalSet U (fun n => (F n : Set (ZMod (q n : ℕ)))) =ᵐ[loebMeasure U hU]
      internalSet U
        (fun n => (cyclicWindow A 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  exact loeb_finset_ae_eq_of_same_density U hU q F
    (fun n => cyclicWindow A 0 (q n : ℕ)) a hFsub hFmass
    (zero_window_counts_tendsto q hq A a hA)

theorem loeb_null_prefix_indicator
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (B : Set ℕ) (E : ℕ → Set ℕ)
    (W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) W)
    (hP0 : internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hzero : loebMeasure U hU p.left.active = 0) :
    ∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))),
      (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      ∀ r : ZMod (h : ℕ), actualWindowProfile U hU q h B (fun _ => 0) r =
        if r ∈ R then (1 : ℝ) else 0 := by
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  have hperiod : ∀ t ∈ p.period, t +ᵥ P =ᵐ[loebMeasure U hU] P :=
    loeb_quasiPeriodic_null_active_ae_periods U hU q P p.period p.left hzero
  obtain ⟨h, R, hd, hmask⟩ := loeb_ae_periods_have_natural_mask U hU q P
    (measurable_internalSet U _) p.period p.period_measurable p.period_positive hperiod
  have hBmask : internalSet U
      (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) :=
    hP0.symm.trans hmask
  refine ⟨h, R, hd, ?_⟩
  intro r
  have hr := actual_window_profile_of_residue_mask U hU q h hd B (fun _ => 0) R hBmask r
  simpa only [Nat.cast_zero, finiteValue_const, add_zero, Finset.image_id'] using hr

end Erdos335.Loeb

end
