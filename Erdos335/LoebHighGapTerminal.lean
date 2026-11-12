import Erdos335.LoebPrefixAgreement
import Erdos335.LoebActualWindowInverse
import Erdos335.LoebPeriodicGapAlternative
import Erdos335.LoebBohrPairAlignment
import Erdos335.LoebBohrPairSwap

/-!
# Positive local terminals under two high capacity-gap bounds

Privately checked supporting development.
The prefix-to-zero-window agreement is an explicit model premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance highGapTerminalLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_high_gap_positive_terminal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b))
    (hgap : a + b < gamma A B)
    (hhighA : gamma A B < a + b + δA)
    (hhighB : gamma A B < a + b + δB)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (D : ∀ n, Set (ZMod (q n : ℕ))) (E : ℕ → Set ℕ)
    (hDsub : internalSet U D ⊆ internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hDAE : internalSet U D =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hEsub : ∀ᶠ n in U, E n ⊆ B) (hexhaust : ∀ v ∈ B, ∀ᶠ n in U, v ∈ E n)
    (hP0 : internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))
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
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    let W := internalSet U D
    let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
    loebMeasure U hU (W + P) = loebMeasure U hU W + loebMeasure U hU P ∧
      (W + P =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) ∧
      (Nonempty (InternalBohrPairData U hU q W P) ∨
        ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) W P,
          ∃ d : InternalBohrPairData U hU q p.left.active p.right.active,
            p.period = (finiteQuotient U d.residue).ker) := by
  classical
  dsimp only
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let W := internalSet U D
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let C := internalSet U
    (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hδA : 0 < δA := by linarith
  have hδB : 0 < δB := by linarith
  have hnoMask (m : ℕ+) (R : Finset (ZMod (m : ℕ)))
      (hmask : internalSet U
        (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
          =ᵐ[μ] (finiteQuotient U (fun n => naturalCyclicProjection (q n) m)) ⁻¹' (R : Set _)) :
      False := by
    have hprofile := actual_window_profile_of_residue_mask U hU q m (hdiv m) A start R hmask
    have hcases := periodic_input_gap_alternative U hU q hdiv hq A B start a b δA δB
      ha hb hδA hδB hmA hmB hmC hgap hcapA hcapB m
      (R.image (fun r => r + finiteValue U (fun n => (start n : ZMod (m : ℕ))))) hprofile
    rcases hcases with h | h
    · exact not_le_of_gt hhighA h
    · exact not_le_of_gt hhighB h
  have hmW : (μ W).toReal = a :=
    (congrArg ENNReal.toReal (measure_congr hDAE)).trans hmA
  have hSm : MeasurableSet (W + P) := by
    dsimp only [W, P]
    rw [← internalSet_add]
    exact measurable_internalSet U _
  have hnotSmall : ¬ μ (W + P) < μ W + μ P := by
    intro hsmall
    obtain ⟨m, R, _, hmask, _⟩ := subcritical_window_is_periodic U hU q hq A B start a b
      ha hb D E hDsub hDAE hEsub hexhaust hmA hmB hmC hmE hsum hsmall hgap
    exact hnoMask m R hmask
  have htotals : μ C = μ W + μ P := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (by finiteness)).mp
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hmW, hmE, hmC]
  have heq : μ (W + P) = μ C := by
    apply le_antisymm (measure_mono_ae hsum)
    rw [htotals]
    exact le_of_not_gt hnotSmall
  have hfull : μ (W + P) = μ W + μ P := heq.trans htotals
  have hmodelC : W + P =ᵐ[μ] C :=
    ae_eq_of_ae_subset_of_measure_ge hsum heq.symm.le hSm.nullMeasurableSet (measure_ne_top μ _)
  refine ⟨hfull, hmodelC, ?_⟩
  rcases loeb_actual_window_inverse U hU q hq A B start a b δB ha hb hδB D E
      hDsub hDAE hEsub hexhaust hmA hmB hmC hmE hsum hgap hcapB with
    hperiodic | hwhole | ⟨p, hterminal⟩
  · obtain ⟨m, R, _, hmask⟩ := hperiodic
    exact False.elim (hnoMask m R hmask)
  · obtain ⟨d⟩ := hwhole
    exact Or.inl ⟨d.swap⟩
  · rcases hterminal with hzero | hbohr
    · obtain ⟨m, R, _, hprofile⟩ := loeb_null_prefix_indicator U hU q B E W p hP0 hzero
      have hmA0 := loeb_zero_window_mass_of_density U hU q hq A a hAdensity
      have hmB0 := loeb_zero_window_mass_of_density U hU q hq B b hBdensity
      have hmC0 := loeb_zero_window_mass_of_density U hU q hq (A + B) (a + b) hCdensity
      have hgammaSwap : gamma B A = gamma A B := by
        unfold gamma modularCapacity
        simp only [add_comm]
      have hcases := periodic_input_gap_alternative U hU q hdiv hq B A (fun _ => 0) b a δB δA
        hb ha hδB hδA hmB0 hmA0
        (by simpa only [add_comm B A, add_comm b a] using hmC0)
        (by simpa only [hgammaSwap, add_comm b a] using hgap) hcapB hcapA m R hprofile
      rcases hcases with h | h
      · have hbound : a + b + δB ≤ gamma A B := by
          simpa only [hgammaSwap, add_comm b a] using h
        exact False.elim (not_le_of_gt hhighB hbound)
      · have hbound : a + b + δA ≤ gamma A B := by
          simpa only [hgammaSwap, add_comm b a] using h
        exact False.elim (not_le_of_gt hhighA hbound)
    · obtain ⟨d⟩ := hbohr
      exact Or.inr (exists_aligned_quasiPeriodicBohrPair U hU q W P p.swap d.swap)

end Erdos335.Loeb

end
