import Erdos335.ConstrainedCyclicModels
import Erdos335.CyclicWindowLiteralLift
import Erdos335.CyclicWindowDensityGeneral
import Erdos335.LoebCyclicModelContainment
import Erdos335.LoebPrefixAgreement

/-!
# Loeb data retaining the fixed constrained window scale

Private proof development. Verification status is recorded separately. This adapter performs no new scale or start
selection. Its finite inputs are the output of a constrained cyclic model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance constrainedAdapterLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem constrained_cyclic_to_loeb
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ℕ) (a b c : ℝ) (hB : HasDensity B b)
    (N H start : ℕ → ℕ) (q : ℕ → ℕ+)
    (hH : ∀ n, 0 < H n) (hHq : ∀ n, H n ≤ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (hinside : ∀ᶠ n in atTop, start n + (q n : ℕ) ≤ N n)
    (hAerror : Tendsto (fun n => prefixError A a (N n) / H n) atTop (𝓝 0))
    (hBerror : Tendsto (fun n => prefixError B b (N n) / H n) atTop (𝓝 0))
    (D P : ∀ n, Finset (ZMod (q n : ℕ)))
    (hsub : ∀ n, D n ⊆ cyclicWindow A (start n) (q n : ℕ) ∧
      P n ⊆ cyclicWindow B 0 (q n : ℕ))
    (hexhaust : ∀ v ∈ B, ∀ᶠ n in atTop, (v : ZMod (q n : ℕ)) ∈ P n)
    (hDcount : Tendsto (fun n => ((D n).card : ℝ) / (q n : ℕ)) atTop (𝓝 a))
    (hPcount : Tendsto (fun n => ((P n).card : ℝ) / (q n : ℕ)) atTop (𝓝 b))
    (hCcount : Tendsto (fun n => ((cyclicWindow (A + B) (start n) (q n : ℕ)).card : ℝ) /
      (q n : ℕ)) atTop (𝓝 c))
    (hspill : Tendsto (fun n => (((D n + P n) \
      cyclicWindow (A + B) (start n) (q n : ℕ)).card : ℝ) / (q n : ℕ)) atTop (𝓝 0)) :
    ∃ E : ℕ → Set ℕ,
      (∀ n, E n ⊆ B) ∧
      (∀ v ∈ B, ∀ᶠ n in U, v ∈ E n) ∧
      internalSet U (fun n => (D n : Set (ZMod (q n : ℕ)))) ⊆ internalSet U
        (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ∧
      (internalSet U (fun n => (D n : Set (ZMod (q n : ℕ)))) =ᵐ[loebMeasure U hU]
        internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) ∧
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) =ᵐ[loebMeasure U hU]
        internalSet U (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ))))) ∧
      (loebMeasure U hU (internalSet U
        (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a ∧
      (loebMeasure U hU (internalSet U
        (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b ∧
      (loebMeasure U hU (internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = c ∧
      (loebMeasure U hU
        (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b ∧
      (internalSet U (fun n => (D n : Set (ZMod (q n : ℕ)))) +
        internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) ≤ᵐ[loebMeasure U hU]
          internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) :
            Set (ZMod (q n : ℕ))))) := by
  classical
  let E : ℕ → Set ℕ := fun n => (cyclicLift (P n) : Set ℕ)
  have himage (n : ℕ) : ((↑) : ℕ → ZMod (q n : ℕ)) '' E n =
      (P n : Set (ZMod (q n : ℕ))) := by
    change ((↑) : ℕ → ZMod (q n : ℕ)) '' (cyclicLift (P n) : Set ℕ) = _
    rw [← Finset.coe_image]
    exact congrArg (fun S : Finset (ZMod (q n : ℕ)) => (S : Set (ZMod (q n : ℕ))))
      (cyclicLift_image (P n))
  have transfer (S : Set ℕ) (d : ℝ)
      (herror : Tendsto (fun n => prefixError S d (N n) / H n) atTop (𝓝 0)) :
      Tendsto (fun n => prefixError S d (N n) / (q n : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => div_nonneg (prefixError_nonneg S d (N n)) (Nat.cast_nonneg _))
      (fun n => ?_) herror
    exact div_le_div_of_nonneg_left (prefixError_nonneg S d (N n))
      (by exact_mod_cast hH n) (by exact_mod_cast hHq n)
  have hAwindow := cyclic_window_density_of_general_prefix_error A a N
    (fun n => (q n : ℕ)) start hq hinside (transfer A a hAerror)
  have hBwindow := cyclic_window_density_of_general_prefix_error B b N
    (fun n => (q n : ℕ)) start hq hinside (transfer B b hBerror)
  have hDAE := loeb_finset_ae_eq_of_same_density U hU q D
    (fun n => cyclicWindow A (start n) (q n : ℕ)) a
    (fun n => (hsub n).1) hDcount hAwindow
  have hP0 := loeb_finite_prefix_agreement U hU q hq B b hB P
    (fun n => (hsub n).2) hPcount
  have hEsub (n : ℕ) : E n ⊆ B := cyclicLift_subset B (P n) (hsub n).2
  have hEexhaust : ∀ v ∈ B, ∀ᶠ n in U, v ∈ E n := by
    intro v hv
    exact (cyclicLift_exhaustion B (fun n => (q n : ℕ)) hq P hexhaust v hv).filter_mono hU
  have hDsub : internalSet U (fun n => (D n : Set (ZMod (q n : ℕ)))) ⊆
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
    apply (internalSet_subset_iff U _ _).mpr
    exact Eventually.of_forall fun n => (hsub n).1
  refine ⟨E, hEsub, hEexhaust, hDsub, hDAE, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [himage] using hP0
  · exact loeb_finset_measure_eq U hU q _ a hAwindow
  · exact loeb_finset_measure_eq U hU q _ b hBwindow
  · exact loeb_finset_measure_eq U hU q _ c hCcount
  · simpa only [himage] using loeb_finset_measure_eq U hU q P b hPcount
  · simpa only [himage] using loeb_cyclic_sum_ae_subset U hU q D P
      (fun n => cyclicWindow (A + B) (start n) (q n : ℕ)) hspill

end Erdos335.Loeb

end
