import Erdos335.OrdinaryDensityCyclicModels
import Erdos335.SparsePrefixSubsequence
import Erdos335.CyclicWindowLiteralLift
import Erdos335.CyclicWindowDensityGeneral
import Erdos335.LoebCyclicModelContainment

/-!
# Actual-window Loeb data from ordinary input and output densities
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.IntermediateScale

local instance ordinaryLocalModelLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := Loeb.loebMeasurableSpace U

theorem exists_ordinary_density_loeb_models
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ℕ) (a b c : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) c) :
    ∃ (q : ℕ → ℕ+) (start : ℕ → ℕ)
      (D : ∀ n, Set (ZMod (q n : ℕ))) (E : ℕ → Set ℕ),
      (∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      Tendsto (fun n => (q n : ℕ)) atTop atTop ∧
      Loeb.internalSet U D ⊆ Loeb.internalSet U
        (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ∧
      (Loeb.internalSet U D =ᵐ[Loeb.loebMeasure U hU] Loeb.internalSet U
        (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) ∧
      (∀ᶠ n in U, E n ⊆ B) ∧ (∀ v ∈ B, ∀ᶠ n in U, v ∈ E n) ∧
      (Loeb.loebMeasure U hU (Loeb.internalSet U
        (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a ∧
      (Loeb.loebMeasure U hU (Loeb.internalSet U
        (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b ∧
      (Loeb.loebMeasure U hU (Loeb.internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = c ∧
      (Loeb.loebMeasure U hU (Loeb.internalSet U
        (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b ∧
      (Loeb.internalSet U D + Loeb.internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
        ≤ᵐ[Loeb.loebMeasure U hU] Loeb.internalSet U
          (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) := by
  obtain ⟨σ, hσ, hNmono, hprev⟩ := exists_sparse_prefix_subsequence (fun n : ℕ => n + 1)
    (tendsto_add_atTop_nat 1)
  let N := fun s => σ s + 1
  have hN : Tendsto N atTop atTop := (tendsto_add_atTop_nat 1).comp hσ.tendsto_atTop
  letI (s : ℕ) : NeZero (N s) := ⟨by dsimp [N]; omega⟩
  obtain ⟨τ, H, start, orders, _, _, _, _, _, hall⟩ :=
    exists_two_orientation_models_of_density N hN hNmono.monotone hprev A B a b c hA hB hC U hU
  obtain ⟨_, hq, _, _, hAerror, hBerror, _, hdiv, hinside, D, P, hsub, hExhaust,
      hD, hP, hCcount, hspill⟩ := hall false
  simp only [Bool.cond_false] at hsub hExhaust hD hP
  let q := orders false
  let E := fun n => cyclicLift (P n)
  have himage (n : ℕ) : ((↑) : ℕ → ZMod (q n : ℕ)) '' (E n : Set ℕ) =
      (P n : Set (ZMod (q n : ℕ))) := by
    rw [← Finset.coe_image]
    exact congrArg (fun S : Finset (ZMod (q n : ℕ)) => (S : Set (ZMod (q n : ℕ))))
      (cyclicLift_image (P n))
  have hAwindow := cyclic_window_density_of_general_prefix_error A a (N ∘ τ)
    (fun s => (q s : ℕ)) start hq hinside hAerror
  have hBwindow := cyclic_window_density_of_general_prefix_error B b (N ∘ τ)
    (fun s => (q s : ℕ)) start hq hinside hBerror
  have hDAE := Loeb.loeb_finset_ae_eq_of_same_density U hU q D
    (fun n => cyclicWindow A (start n) (q n : ℕ)) a (fun n => (hsub n).1) hD hAwindow
  have hmD := Loeb.loeb_finset_measure_eq U hU q D a hD
  have hmE : (Loeb.loebMeasure U hU (Loeb.internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' (E n : Set ℕ)))).toReal = b := by
    simpa only [himage] using Loeb.loeb_finset_measure_eq U hU q P b hP
  have hmC := Loeb.loeb_finset_measure_eq U hU q
    (fun n => cyclicWindow (A + B) (start n) (q n : ℕ)) c hCcount
  have hsum : Loeb.internalSet U (fun n => (D n : Set (ZMod (q n : ℕ)))) +
      Loeb.internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' (E n : Set ℕ))
        ≤ᵐ[Loeb.loebMeasure U hU] Loeb.internalSet U
          (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
    simpa only [himage] using Loeb.loeb_cyclic_sum_ae_subset U hU q D P
      (fun n => cyclicWindow (A + B) (start n) (q n : ℕ)) hspill
  have hmA : (Loeb.loebMeasure U hU (Loeb.internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a :=
    (congrArg ENNReal.toReal (measure_congr hDAE)).symm.trans hmD
  refine ⟨q, start, (fun n => (D n : Set (ZMod (q n : ℕ)))), (fun n => (E n : Set ℕ)),
    (fun h => (hdiv h h.pos).filter_mono hU), hq, ?_, hDAE,
    Eventually.of_forall (fun n => cyclicLift_subset B (P n) (hsub n).2),
    (fun v hv => (cyclicLift_exhaustion B (fun n => (q n : ℕ)) hq P hExhaust v hv).filter_mono hU),
    hmA, Loeb.loeb_finset_measure_eq U hU q _ b hBwindow, hmC, hmE, hsum⟩
  apply (Loeb.internalSet_subset_iff U _ _).mpr
  exact Eventually.of_forall (fun n => (hsub n).1)

end Erdos335.IntermediateScale

end
