import Erdos335.LoebHighGapTerminal
import Erdos335.QuasiPositiveProfileConstruction
import Erdos335.WholePositiveProfileConstruction

/-!
# A shared local profile record for either positive terminal alternative

Private proof development. Verification status is recorded separately. Both whole and quasi-positive alternatives are
retained and converted using their separate supporting interfaces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance highGapProfileConstructionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_local_positive_profile_of_high_gaps
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
    ∃ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 ∧
      Nonempty (LocalPositiveResidueProfile h A B a b
      (fun m r => actualWindowProfile U hU q m A start r)
      (fun m r => actualWindowProfile U hU q m B (fun _ => 0) r)
      (fun m r => actualWindowProfile U hU q m (A + B) start r)) := by
  classical
  have hBnonempty : B.Nonempty := by
    by_contra hBempty
    have hemp : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hBempty
    have hzero : HasDensity B 0 := by simpa only [hemp] using hasDensity_empty
    have hbzero := hBdensity.unique hzero
    linarith
  obtain ⟨hfull, hmodelC, hterminal⟩ := loeb_high_gap_positive_terminal U hU q hdiv hq
    A B start a b δA δB ha hb hAdensity hBdensity hCdensity hgap hhighA hhighB
    hcapA hcapB D E hDsub hDAE hEsub hexhaust hP0 hmA hmB hmC hmE hsum
  rcases hterminal with hwhole | ⟨p, d, hperiod⟩
  · obtain ⟨d⟩ := hwhole
    have hSm : MeasurableSet (internalSet U D +
        internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) := by
      rw [← internalSet_add]
      exact measurable_internalSet U _
    obtain ⟨hmassA, hmassB, hgamma, _, _⟩ := whole_bohr_gap_formulas U hU q hdiv hq
      A B hBnonempty start a b hb (internalSet U D) E hDAE hEsub hexhaust
      hmA hmB hmE d hSm hfull hmodelC
    have hDelta : gamma A B - (a + b) =
        (1 - d.left_length - d.right_length) / (d.modulus : ℕ) := by
      rw [hgamma, hmassA, hmassB]
      ring
    have hne : ((d.modulus : ℕ) : ℝ) ≠ 0 := by exact_mod_cast d.modulus.ne_zero
    have hbound : ((d.modulus : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 := by
      calc
        ((d.modulus : ℕ) : ℝ) * (gamma A B - (a + b)) =
            1 - d.left_length - d.right_length := by rw [hDelta]; field_simp [hne]
        _ < 1 := by linarith [d.left_positive, d.right_positive]
    exact ⟨d.modulus, hbound, exists_local_positive_profile_of_whole_bohr U hU q hdiv hq
      A B hBnonempty start a b hb D E hDsub hDAE hEsub hexhaust hP0
      hmA hmB hmE d hfull hmodelC⟩
  · obtain ⟨hDelta, _, _, _⟩ := loeb_positive_terminal_gap_formulas U hU q hdiv hq
      A B start a b D E hDAE hEsub hexhaust hmA hmB hmE p d hperiod hfull hmodelC
    have hne : ((d.modulus : ℕ) : ℝ) ≠ 0 := by exact_mod_cast d.modulus.ne_zero
    have hbound : ((d.modulus : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 := by
      calc
        ((d.modulus : ℕ) : ℝ) * (gamma A B - (a + b)) =
            1 - d.left_length - d.right_length := by rw [hDelta]; field_simp [hne]
        _ < 1 := by linarith [d.left_positive, d.right_positive]
    exact ⟨d.modulus, hbound, exists_local_positive_profile_of_quasi_terminal U hU q hdiv
      A B start a b D E hDsub hDAE hEsub hexhaust hP0 hmA hmE p d hperiod hfull hmodelC⟩

end Erdos335.Loeb

end
