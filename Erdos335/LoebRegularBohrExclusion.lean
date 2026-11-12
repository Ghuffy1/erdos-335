import Erdos335.LoebBohrPairAlignment
import Erdos335.LoebBohrWindowGap
import Erdos335.LoebQuasiBohrWindowGap

/-!
# Positive Bohr terminals are excluded by a zero literal residue-capacity gap
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale

noncomputable section

namespace Erdos335.Loeb

local instance regularBohrExclusionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_regular_window_no_positive_terminal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (P W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (A : Set ℕ) (start : ℕ → ℕ)
    (hWA : W =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (a : ℝ) (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε) :
    ¬ Nonempty (InternalBohrPairData U hU q P W) ∧
      ∀ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) P W,
        ¬ Nonempty (InternalBohrPairData U hU q p.left.active p.right.active) := by
  have gap_false (δ : ℝ) (hδ : 0 < δ)
      (hbound : ∀ h : ℕ+, a + δ ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ)) : False := by
    obtain ⟨k, hk⟩ := happrox (δ / 2) (by linarith)
    have hlow := hbound k
    linarith
  constructor
  · rintro ⟨b⟩
    obtain ⟨δ, hδ, hbound⟩ := internalBohrPair_right_window_gap U hU q hdiv P W b A start hWA a hmA
    exact gap_false δ hδ hbound
  · intro p
    rintro ⟨b⟩
    obtain ⟨r, d, hperiod⟩ := exists_aligned_quasiPeriodicBohrPair U hU q P W p b
    obtain ⟨δ, hδ, hbound⟩ := quasiPeriodicBohr_right_window_gap U hU q hdiv P W r d hperiod A start hWA a hmA
    exact gap_false δ hδ hbound

end Erdos335.Loeb

end
