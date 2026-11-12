import Erdos335.LoebPrefixAgreement
import Erdos335.LoebWholeBohrGap
import Erdos335.LoebActualWindowInverse
import Erdos335.LoebPositiveTerminalGaps
import Erdos335.LoebBohrPairAlignment
import Erdos335.LoebBohrPairSwap

/-!
# Periodic and null-prefix terminals when the prefix input is Low

Private proof development. Verification status is recorded separately.
The quantified Low condition is imposed on the prefix input `B`.
The null-prefix branch retains critical sum equality, actual output agreement,
and an indicator profile for the actual zero-start prefix input `B`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance lowPrefixGapTerminalLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

theorem loeb_low_prefix_gap_periodic_or_null_prefix
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδB : 0 < δB)
    (hgap : a + b < gamma A B)
    (hlowB : ∀ η : ℝ, gamma A B - (a + b) < η →
      ∃ k : ℕ+, ((residues (k : ℕ) B).card : ℝ) / (k : ℕ) < b + η)
    (hcapB : ∀ h : ℕ+, b + δB ≤
      ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (D : ∀ n, Set (ZMod (q n : ℕ))) (E : ℕ → Set ℕ)
    (hDsub : internalSet U D ⊆ internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hDAE : internalSet U D =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hEsub : ∀ᶠ n in U, E n ⊆ B)
    (hexhaust : ∀ v ∈ B, ∀ᶠ n in U, v ∈ E n)
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
    (∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))),
      (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      internalSet U
        (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU]
          (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _)) ∨
    (loebMeasure U hU (W + P) = loebMeasure U hU W + loebMeasure U hU P ∧
      (W + P =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) ∧
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) P W,
        loebMeasure U hU p.left.active = 0 ∧
        ∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))),
          (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
          ∀ r : ZMod (h : ℕ), actualWindowProfile U hU q h B (fun _ => 0) r =
            if r ∈ R then (1 : ℝ) else 0) := by
  classical
  dsimp only
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let W := internalSet U D
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let C := internalSet U
    (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hnoTerminal (m : ℕ+) (x y : ℝ) (hx : 0 < x)
      (hDelta : gamma A B - (a + b) = (1 - x - y) / (m : ℕ))
      (hcap : ∀ k : ℕ+, b + (1 - y) / (m : ℕ) ≤
        ((residues (k : ℕ) B).card : ℝ) / (k : ℕ)) : False := by
    have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
    have hpositive : 0 < x / (m : ℕ) := div_pos hx hmpos
    have hdifference : (1 - y) / (m : ℕ) - (gamma A B - (a + b)) =
        x / (m : ℕ) := by
      rw [hDelta]
      ring
    have hη : gamma A B - (a + b) < (1 - y) / (m : ℕ) := by linarith
    obtain ⟨k, hk⟩ := hlowB ((1 - y) / (m : ℕ)) hη
    exact (not_lt_of_ge (hcap k)) hk
  have hBnonempty : B.Nonempty := by
    by_contra hB
    have hBempty : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    have hbound := hcapB (1 : ℕ+)
    have hnonpos : b + δB ≤ 0 := by simpa [hBempty, residues] using hbound
    linarith
  have hmW : (μ W).toReal = a :=
    (congrArg ENNReal.toReal (measure_congr hDAE)).trans hmA
  have hSm : MeasurableSet (W + P) := by
    dsimp only [W, P]
    rw [← internalSet_add]
    exact measurable_internalSet U _
  by_cases hsmall : μ (W + P) < μ W + μ P
  · obtain ⟨h, R, hd, hmask, _⟩ := subcritical_window_is_periodic U hU q hq A B start a b
      ha hb D E hDsub hDAE hEsub hexhaust hmA hmB hmC hmE hsum hsmall hgap
    exact Or.inl ⟨h, R, hd, hmask⟩
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
  rcases loeb_actual_window_inverse U hU q hq A B start a b δB ha hb hδB D E
      hDsub hDAE hEsub hexhaust hmA hmB hmC hmE hsum hgap hcapB with
    hperiodic | hwhole | ⟨p, hterminal⟩
  · exact Or.inl hperiodic
  · obtain ⟨d⟩ := hwhole
    let d' := d.swap
    obtain ⟨haLength, hbLength, hgamma, _, hcapPrefix⟩ :=
      whole_bohr_gap_formulas U hU q hdiv hq A B hBnonempty start a b hb W E
        hDAE hEsub hexhaust hmA hmB hmE d' hSm hfull hmodelC
    have hDelta : gamma A B - (a + b) =
        (1 - d'.left_length - d'.right_length) / (d'.modulus : ℕ) := by
      rw [hgamma, haLength, hbLength]
      ring
    exact False.elim (hnoTerminal d'.modulus d'.left_length d'.right_length
      d'.left_positive hDelta hcapPrefix)
  · rcases hterminal with hzero | hbohr
    · refine Or.inr ⟨hfull, hmodelC, p, hzero, ?_⟩
      exact loeb_null_prefix_indicator U hU q B E W p hP0 hzero
    · obtain ⟨d⟩ := hbohr
      obtain ⟨r, d', hperiod⟩ :=
        exists_aligned_quasiPeriodicBohrPair U hU q W P p.swap d.swap
      obtain ⟨hDelta, _, hcapPrefix, _⟩ :=
        loeb_positive_terminal_gap_formulas U hU q hdiv hq A B start a b D E
          hDAE hEsub hexhaust hmA hmB hmE r d' hperiod hfull hmodelC
      exact False.elim (hnoTerminal d'.modulus d'.left_length d'.right_length
        d'.left_positive hDelta hcapPrefix)

end Erdos335.Loeb

end
