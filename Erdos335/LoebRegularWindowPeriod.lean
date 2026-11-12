import Erdos335.LoebResidueApproximationPeriod

/-!
# A finite mask for a regular actual window with one integer period
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance regularWindowPeriodLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_regular_window_period_is_mask
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (a : ℝ)
    (hmass : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε)
    (t : ℕ+)
    (hperiod : productProjection (U : Filter ℕ) (fun n => ((t : ℕ) : ZMod (q n : ℕ))) +ᵥ
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU]
        internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    ∃ R : Finset (ZMod (t : ℕ)),
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU] (finiteQuotient U (fun n => naturalCyclicProjection (q n) t)) ⁻¹' (R : Set _) := by
  apply loeb_periodic_mask_of_residue_approximation U hU q hdiv _ (measurable_internalSet U _) a hmass ?_ t hperiod
  intro ε hε
  obtain ⟨k, hk⟩ := happrox ε hε
  let z := finiteValue U (fun n => (start n : ZMod (k : ℕ)))
  let R := (residues (k : ℕ) A).image (fun r => r - z)
  have hsub := actual_window_residue_subset U q k (hdiv k) A start
  rw [windowResidueMap_preimage] at hsub
  refine ⟨k, R, hsub.eventuallySubset, ?_⟩
  have hcard : R.card = (residues (k : ℕ) A).card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    have he := congrArg (fun r => r + z) hxy
    simpa only [sub_add_cancel] using he
  rw [hcard]
  exact hk

end Erdos335.Loeb

end
