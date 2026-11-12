import Erdos335.LowGapPairedWindows
import Erdos335.LoebLowGapTerminal
import Erdos335.LoebLowPrefixTerminal
import Erdos335.LoebUniformPeriodicInput

/-!
# Periodic actual windows in the paired Low branch

Private proof development. Verification status is recorded separately. The quantified Low condition is imposed on A.
The two orientations use one physical start and nearby cyclic lengths.
The periodic moving input is derived from the terminal alternatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance lowPeriodicWindowsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

theorem loeb_low_gap_paired_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : Bool → ℕ → ℕ+)
    (hdiv : ∀ o, ∀ h : ℕ+, ∀ᶠ n in atTop, (h : ℕ) ∣ (q o n : ℕ))
    (hq : ∀ o, Tendsto (fun n => (q o n : ℕ)) atTop atTop)
    (H : ℕ → ℕ) (hH : ∀ n, 0 < H n) (hHq : ∀ o n, H n ≤ (q o n : ℕ))
    (hqgap : ∀ o, Tendsto (fun n => (((q o n : ℕ) - H n : ℕ) : ℝ) /
      (q o n : ℕ)) atTop (𝓝 0))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hlowA : ∀ η : ℝ, gamma A B - (a + b) < η →
      ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (D : ∀ o n, Set (ZMod (q o n : ℕ))) (E : Bool → ℕ → Set ℕ)
    (hDsub : ∀ o, internalSet U (D o) ⊆ internalSet U
      (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))
    (hDAE : ∀ o, internalSet U (D o) =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))
    (hEsub : ∀ o, ∀ᶠ n in U, E o n ⊆ (if o then A else B))
    (hexhaust : ∀ o, ∀ v ∈ (if o then A else B), ∀ᶠ n in U, v ∈ E o n)
    (hP0 : ∀ o, internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (if o then A else B) 0 (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))
    (hmMoving : ∀ o, (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal =
        (if o then b else a))
    (hmOther : ∀ o, (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (if o then A else B) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal =
        (if o then a else b))
    (hmC : ∀ o, (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal = a + b)
    (hmE : ∀ o, (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n))).toReal =
        (if o then a else b))
    (hsum : ∀ o, internalSet U (D o) +
      internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
        ≤ᵐ[loebMeasure U hU] internalSet U
          (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ))))) :
    ∃ (o : Bool) (m : ℕ+) (P : Finset (ZMod (m : ℕ))),
      ∀ r, actualWindowProfile U hU (q o) m (if o then B else A) start r =
        if r ∈ P then (1 : ℝ) else 0 := by
  classical
  have hdivU : ∀ o, ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q o n : ℕ) :=
    fun o h => (hdiv o h).filter_mono hU
  have hgammaSwap : gamma B A = gamma A B := by
    unfold gamma modularCapacity
    simp only [add_comm]
  have hForward := loeb_low_gap_periodic_or_null_prefix U hU (q false)
    (hdivU false) (hq false) A B start a b δB ha hb hδB hgap hlowA hcapB
    (D false) (E false) (hDsub false) (hDAE false) (hEsub false) (hexhaust false)
    (hP0 false) (hmMoving false) (hmOther false) (hmC false) (hmE false) (hsum false)
  have hReverse := loeb_low_prefix_gap_periodic_or_null_prefix U hU (q true)
    (hdivU true) (hq true) B A start b a δA hb ha hδA
    (by simpa only [hgammaSwap, add_comm b a] using hgap)
    (by simpa only [hgammaSwap, add_comm b a] using hlowA) hcapA
    (D true) (E true) (hDsub true) (hDAE true) (hEsub true) (hexhaust true)
    (hP0 true) (hmMoving true) (hmOther true)
    (by simpa only [add_comm A B, add_comm a b] using hmC true) (hmE true)
    (by simpa only [add_comm A B] using hsum true)
  have hPeriodic :
      (∃ (m : ℕ+) (P : Finset (ZMod (m : ℕ))),
        (∀ᶠ n in U, (m : ℕ) ∣ (q false n : ℕ)) ∧
          internalSet U
            (fun n => (cyclicWindow A (start n) (q false n : ℕ) : Set (ZMod (q false n : ℕ))))
            =ᵐ[loebMeasure U hU]
              (finiteQuotient U (fun n => naturalCyclicProjection (q false n) m)) ⁻¹' (P : Set _)) ∨
      (∃ (m : ℕ+) (P : Finset (ZMod (m : ℕ))),
        (∀ᶠ n in U, (m : ℕ) ∣ (q true n : ℕ)) ∧
          internalSet U
            (fun n => (cyclicWindow B (start n) (q true n : ℕ) : Set (ZMod (q true n : ℕ))))
            =ᵐ[loebMeasure U hU]
              (finiteQuotient U (fun n => naturalCyclicProjection (q true n) m)) ⁻¹' (P : Set _)) := by
    rcases hForward with hperiodic | ⟨_, _, pA, hzeroA, _⟩
    · exact Or.inl hperiodic
    rcases hReverse with hperiodic | ⟨_, _, pB, hzeroB, _⟩
    · exact Or.inr hperiodic
    have hmW (o : Bool) : (loebMeasure U hU (internalSet U (D o))).toReal =
        if o then b else a :=
      (congrArg ENNReal.toReal (measure_congr (hDAE o))).trans (hmMoving o)
    exact loeb_two_null_prefix_models_force_periodic U hU (q false) (q true) H
      (hdiv false) (hdiv true) (hq false) hH (hHq false) (hHq true)
      (hqgap false) (hqgap true) A B start a b ha hb hAdensity hBdensity hCdensity hgap
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q false n : ℕ)) '' E false n))
      (internalSet U (D false))
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q true n : ℕ)) '' E true n))
      (internalSet U (D true)) pA pB
      (hP0 false) (hDAE false) (hP0 true) (hDAE true)
      (hmE false) (hmW false) (hmE true) (hmW true) hzeroA hzeroB
  rcases hPeriodic with ⟨m, P, hd, hmask⟩ | ⟨m, P, hd, hmask⟩
  · refine ⟨false, m, P.image (fun t => t + finiteValue U
      (fun n => (start n : ZMod (m : ℕ)))), ?_⟩
    exact actual_window_profile_of_residue_mask U hU (q false) m hd A start P hmask
  · refine ⟨true, m, P.image (fun t => t + finiteValue U
      (fun n => (start n : ZMod (m : ℕ)))), ?_⟩
    exact actual_window_profile_of_residue_mask U hU (q true) m hd B start P hmask

theorem exists_uniform_low_gap_window_witnesses
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hlowA : ∀ η : ℝ, gamma A B - (a + b) < η →
      ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) :
    ∃ (M : ℕ+) (FA FB : Finset ℕ), (FA : Set ℕ) ⊆ A ∧ (FB : Set ℕ) ⊆ B ∧
      ∀ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : Bool → ℕ → ℕ+)
        (hdiv : ∀ o, ∀ h : ℕ+, ∀ᶠ n in atTop, (h : ℕ) ∣ (q o n : ℕ))
        (hq : ∀ o, Tendsto (fun n => (q o n : ℕ)) atTop atTop)
        (H : ℕ → ℕ) (hH : ∀ n, 0 < H n) (hHq : ∀ o n, H n ≤ (q o n : ℕ))
        (hqgap : ∀ o, Tendsto (fun n => (((q o n : ℕ) - H n : ℕ) : ℝ) /
          (q o n : ℕ)) atTop (𝓝 0))
        (start : ℕ → ℕ) (D : ∀ o n, Set (ZMod (q o n : ℕ))) (E : Bool → ℕ → Set ℕ)
        (hDsub : ∀ o, internalSet U (D o) ⊆ internalSet U
          (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) :
            Set (ZMod (q o n : ℕ)))))
        (hDAE : ∀ o, internalSet U (D o) =ᵐ[loebMeasure U hU] internalSet U
          (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) :
            Set (ZMod (q o n : ℕ)))))
        (hEsub : ∀ o, ∀ᶠ n in U, E o n ⊆ (if o then A else B))
        (hexhaust : ∀ o, ∀ v ∈ (if o then A else B), ∀ᶠ n in U, v ∈ E o n)
        (hP0 : ∀ o, internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
          =ᵐ[loebMeasure U hU] internalSet U
            (fun n => (cyclicWindow (if o then A else B) 0 (q o n : ℕ) :
              Set (ZMod (q o n : ℕ)))))
        (hmMoving : ∀ o, (loebMeasure U hU (internalSet U
          (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) :
            Set (ZMod (q o n : ℕ)))))).toReal = (if o then b else a))
        (hmOther : ∀ o, (loebMeasure U hU (internalSet U
          (fun n => (cyclicWindow (if o then A else B) (start n) (q o n : ℕ) :
            Set (ZMod (q o n : ℕ)))))).toReal = (if o then a else b))
        (hmC : ∀ o, (loebMeasure U hU (internalSet U
          (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) :
            Set (ZMod (q o n : ℕ)))))).toReal = a + b)
        (hmE : ∀ o, (loebMeasure U hU
          (internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n))).toReal =
            (if o then a else b))
        (hsum : ∀ o, internalSet U (D o) +
          internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
            ≤ᵐ[loebMeasure U hU] internalSet U
              (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) :
                Set (ZMod (q o n : ℕ))))),
        ∃ (o : Bool) (h : ℕ+),
          ((h : ℕ) : ℝ) ≤ max (1 / δA) (max (1 / δB) (1 / (gamma A B - (a + b)))) ∧
          (ActualWindowNullFrame U hU (q o) h A B start a ∨
            ActualWindowNullFrame U hU (q o) h B A start b) ∧
          let W := fun S : Set ℕ => internalSet U
            (fun n => (cyclicWindow S (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ))))
          let t := productProjection (U : Filter ℕ) (fun n => ((M : ℕ) : ZMod (q o n : ℕ)))
          (t +ᵥ W A =ᵐ[loebMeasure U hU] W A) ∧
          (t +ᵥ W B =ᵐ[loebMeasure U hU] W B) ∧
          (t +ᵥ W (A + B) =ᵐ[loebMeasure U hU] W (A + B)) ∧
          W (A + B) =ᵐ[loebMeasure U hU] W (Proposed.finiteTranslateCover A B FA FB) := by
  classical
  obtain ⟨M, FA, FB, hFA, hFB, hUniform⟩ := exists_uniform_periodic_input_witnesses
    A B a b δA δB ha hb hδA hδB hgap hcapA hcapB
  refine ⟨M, FA, FB, hFA, hFB, ?_⟩
  intro U hU q hdiv hq H hH hHq hqgap start D E hDsub hDAE hEsub hexhaust
    hP0 hmMoving hmOther hmC hmE hsum
  obtain ⟨o, m, P, hP⟩ := loeb_low_gap_paired_periodic U hU q hdiv hq H hH hHq hqgap
    A B start a b δA δB ha hb hδA hδB hAdensity hBdensity hCdensity hgap hlowA
    hcapA hcapB D E hDsub hDAE hEsub hexhaust hP0 hmMoving hmOther hmC hmE hsum
  have hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal = a := by
    cases o
    · exact hmMoving false
    · exact hmOther true
  have hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal = b := by
    cases o
    · exact hmOther false
    · exact hmMoving true
  have hmask : (∀ r, actualWindowProfile U hU (q o) m A start r = if r ∈ P then (1 : ℝ) else 0) ∨
      (∀ r, actualWindowProfile U hU (q o) m B start r = if r ∈ P then (1 : ℝ) else 0) := by
    cases o
    · exact Or.inl hP
    · exact Or.inr hP
  obtain ⟨h, _, hbound, hframe, hdata⟩ := hUniform U hU (q o)
    (fun r => (hdiv o r).filter_mono hU) (hq o) start hmA hmB (hmC o) m P hmask
  exact ⟨o, h, hbound, hframe, hdata⟩

end Erdos335.Loeb

end
