import Erdos335.LowGapPeriodicWindows
import Erdos335.LowGapOrdinaryTransfer
import Erdos335.LoebFixedShiftWindow
import Erdos335.MaskCoverage
import Erdos335.RegularClassification

/-!
# Ordinary necessity in the Low branch

Private proof development. Verification status is recorded separately. Fixed local periods and finite covers are
transferred through the constrained-window null-defect theorem, then the
ordinary mask criterion supplies the classified branch.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal symmDiff

noncomputable section

namespace Erdos335.Loeb

local instance lowNecessityLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

private theorem actual_window_union
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (A B : Set ℕ) (start : ℕ → ℕ) :
    internalSet U (fun n => (cyclicWindow (A ∪ B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) =
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ∪
        internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  classical
  calc
    _ = internalSet U (fun n =>
        (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))) ∪
          (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
      congr 1
      funext n
      ext x
      simp [cyclicWindow]
    _ = _ := internalSet_union U _ _

private theorem actual_window_symmDiff
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (A B : Set ℕ) (start : ℕ → ℕ) :
    internalSet U (fun n => (cyclicWindow (A ∆ B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) =
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ∆
        internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  classical
  calc
    _ = internalSet U (fun n =>
        (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))) ∆
          (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
      congr 1
      funext n
      ext x
      simp [cyclicWindow, Set.symmDiff_def]
    _ = _ := by
      simp only [Set.symmDiff_def, internalSet_union, internalSet_sdiff]

private theorem actual_window_symmDiff_null_of_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ℕ) (start : ℕ → ℕ)
    (hAB : internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A ∆ B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) = 0 := by
  rw [actual_window_symmDiff]
  exact measure_symmDiff_eq_zero_iff.mpr hAB

theorem low_gap_ordinary_equivalences
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hlowA : ∀ η : ℝ, gamma A B - (a + b) < η →
      ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) :
    ∃ (M : ℕ+) (FA FB : Finset ℕ), (FA : Set ℕ) ⊆ A ∧ (FB : Set ℕ) ⊆ B ∧
      DensityEquivalent (shift A (M : ℕ)) A ∧
      DensityEquivalent (shift B (M : ℕ)) B ∧
      DensityEquivalent (A + B) (Proposed.finiteTranslateCover A B FA FB) := by
  classical
  obtain ⟨M, FA, FB, hFA, hFB, hUniform⟩ := exists_uniform_low_gap_window_witnesses
    A B a b δA δB ha hb hδA hδB hAdensity hBdensity hCdensity hgap hlowA hcapA hcapB
  let T := ((shift A (M : ℕ) ∆ A) ∪ (shift B (M : ℕ) ∆ B)) ∪
    ((A + B) ∆ Proposed.finiteTranslateCover A B FA FB)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hT : Negligible T := by
    apply negligible_of_constrained_window_null U hU A B T a b (a + b)
      hAdensity hBdensity hCdensity
    intro q hdiv hq H hH hHq hqgap start D E hDsub hDAE hEsub hexhaust
      hP0 hmMoving hmOther hmC hmE hsum
    obtain ⟨o, _, _, _, hdata⟩ := hUniform U hU q hdiv hq H hH hHq hqgap
      start D E hDsub hDAE hEsub hexhaust hP0 hmMoving hmOther hmC hmE hsum
    let W := fun S : Set ℕ => internalSet U
      (fun n => (cyclicWindow S (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ))))
    let t := productProjection (U : Filter ℕ) (fun n => ((M : ℕ) : ZMod (q o n : ℕ)))
    change (t +ᵥ W A =ᵐ[loebMeasure U hU] W A) ∧
      (t +ᵥ W B =ᵐ[loebMeasure U hU] W B) ∧
      (t +ᵥ W (A + B) =ᵐ[loebMeasure U hU] W (A + B)) ∧
      W (A + B) =ᵐ[loebMeasure U hU] W (Proposed.finiteTranslateCover A B FA FB) at hdata
    obtain ⟨hPeriodA, hPeriodB, _, hCover⟩ := hdata
    have hAwindow : W (shift A (M : ℕ)) =ᵐ[loebMeasure U hU] W A :=
      (loeb_fixed_shift_window_eq U hU (q o) (hq o) A start (M : ℕ)).symm.trans hPeriodA
    have hBwindow : W (shift B (M : ℕ)) =ᵐ[loebMeasure U hU] W B :=
      (loeb_fixed_shift_window_eq U hU (q o) (hq o) B start (M : ℕ)).symm.trans hPeriodB
    have hAdefect := actual_window_symmDiff_null_of_ae U hU (q o)
      (shift A (M : ℕ)) A start hAwindow
    have hBdefect := actual_window_symmDiff_null_of_ae U hU (q o)
      (shift B (M : ℕ)) B start hBwindow
    have hCdefect := actual_window_symmDiff_null_of_ae U hU (q o)
      (A + B) (Proposed.finiteTranslateCover A B FA FB) start hCover
    refine ⟨o, ?_⟩
    dsimp only [T]
    rw [actual_window_union, actual_window_union]
    exact measure_union_null (measure_union_null hAdefect hBdefect) hCdefect
  have hAdefect : Negligible (shift A (M : ℕ) ∆ A) := by
    apply hT.mono
    intro n hn
    exact Or.inl (Or.inl hn)
  have hBdefect : Negligible (shift B (M : ℕ) ∆ B) := by
    apply hT.mono
    intro n hn
    exact Or.inl (Or.inr hn)
  have hCdefect : Negligible ((A + B) ∆ Proposed.finiteTranslateCover A B FA FB) := by
    apply hT.mono
    intro n hn
    exact Or.inr hn
  refine ⟨M, FA, FB, hFA, hFB, ?_, ?_, ?_⟩
  · apply (densityEquivalent_iff_symmetric_difference _ _).mpr
    simpa only [Set.symmDiff_def] using hAdefect
  · apply (densityEquivalent_iff_symmetric_difference _ _).mpr
    simpa only [Set.symmDiff_def] using hBdefect
  · apply (densityEquivalent_iff_symmetric_difference _ _).mpr
    simpa only [Set.symmDiff_def] using hCdefect

end Erdos335.Loeb

namespace Erdos335.Proposed

theorem low_gap_mask_branch
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hlowA : ∀ η : ℝ, gamma A B - (a + b) < η →
      ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) :
    MaskBranch A B (a + b) := by
  obtain ⟨M, FA, FB, hFA, hFB, hAperiod, hBperiod, hCover⟩ :=
    Loeb.low_gap_ordinary_equivalences A B a b δA δB ha hb hδA hδB
      hAdensity hBdensity hCdensity hgap hlowA hcapA hcapB
  exact (maskBranch_iff_common_period_finite_translate_cover A B (a + b)).mpr
    ⟨hCdensity, M, FA, FB, hAperiod, hBperiod, hFA, hFB, hCover.1⟩

theorem low_gap_classified
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hlowA : ∀ η : ℝ, gamma A B - (a + b) < η →
      ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) :
    Classified A B (a + b) := by
  exact Or.inr ⟨hgap, Or.inr (Or.inr (low_gap_mask_branch A B a b δA δB ha hb hδA hδB
    hAdensity hBdensity hCdensity hgap hlowA hcapA hcapB))⟩

theorem low_gap_classified_of_either
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hlow :
      (∀ η : ℝ, gamma A B - (a + b) < η →
        ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η) ∨
      (∀ η : ℝ, gamma A B - (a + b) < η →
        ∃ k : ℕ+, ((residues (k : ℕ) B).card : ℝ) / (k : ℕ) < b + η))
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) :
    Classified A B (a + b) := by
  rcases hlow with hlowA | hlowB
  · exact low_gap_classified A B a b δA δB ha hb hδA hδB
      hAdensity hBdensity hCdensity hgap hlowA hcapA hcapB
  · have hgammaSwap : gamma B A = gamma A B := by
      unfold gamma modularCapacity
      simp only [add_comm]
    have hMask : MaskBranch B A (b + a) := low_gap_mask_branch B A b a δB δA hb ha hδB hδA
      hBdensity hAdensity
      (by simpa only [add_comm A B, add_comm a b] using hCdensity)
      (by simpa only [hgammaSwap, add_comm b a] using hgap)
      (by simpa only [hgammaSwap, add_comm b a] using hlowB) hcapB hcapA
    have hMaskSwap : MaskBranch A B (a + b) := by
      simpa only [add_comm b a] using hMask.swap
    exact Or.inr ⟨hgap, Or.inr (Or.inr hMaskSwap)⟩

end Erdos335.Proposed

end
