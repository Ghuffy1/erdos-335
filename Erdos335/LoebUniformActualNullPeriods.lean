import Erdos335.FiniteNullCapacity
import Erdos335.FiniteDifferenceRepresentatives
import Erdos335.LoebNullFramePeriods

/-!
# A finite family of periods for every actual-window null frame
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance uniformActualNullPeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_uniform_actual_null_periods
    (A : Set ℕ) (a δ : ℝ) (hδ : 0 < δ)
    (hcapacity : ∀ k : ℕ+, a + δ ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ)) :
    ∃ D : Finset ℕ, (∀ t ∈ D, 0 < t) ∧
      ∀ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+),
        Tendsto (fun n => (q n : ℕ)) atTop atTop →
        ∀ (h : ℕ+), (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) →
        ∀ (B : Set ℕ) (start : ℕ → ℕ) (b : ℝ) (i j : ZMod (h : ℕ)),
          i ∈ residues (h : ℕ) A → j ∈ residues (h : ℕ) B →
          a = (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ) →
          (loebMeasure U hU (internalSet U
            (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b →
          (loebMeasure U hU (internalSet U
            (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b →
          (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
            (residues (h : ℕ) A).card + (residues (h : ℕ) B).card →
          (∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1) →
          (∀ r ∈ (residues (h : ℕ) B).erase j, actualWindowProfile U hU q h B start r = 1) →
          ∃ t ∈ D,
            productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ))) +ᵥ
              internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
                =ᵐ[loebMeasure U hU]
                  internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ∧
            productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ))) +ᵥ
              internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
                =ᵐ[loebMeasure U hU]
                  internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  let N := Nat.ceil (1 / δ)
  obtain ⟨D, hD, hselect⟩ := finite_residue_difference_representatives A N
  refine ⟨D, hD, ?_⟩
  intro U hU q hq h hd B start b i j hi hj ha hmB hmC hcard hAfull hBfull
  have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hδh : δ ≤ 1 / (h : ℕ) := by
    have hc := hcapacity h
    rw [ha] at hc
    have heq : (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ) + 1 / (h : ℕ) =
        ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by ring
    linarith
  have hindex : ((h : ℕ) : ℝ) ≤ 1 / δ := by
    apply (le_div_iff₀ hδ).mpr
    have hp := (le_div_iff₀ hh).mp hδh
    simpa only [mul_comm] using hp
  have hleN : (h : ℕ) ≤ N := by exact_mod_cast hindex.trans (Nat.le_ceil (1 / δ))
  obtain ⟨u, hu, v, hv, huv, hui, hvi, hdiff⟩ := hselect h i hleN
    (positive_gap_null_class_has_two_points A a δ hδ hcapacity h i hi ha)
  exact ⟨v - u, hdiff, null_frame_integer_difference_periods U hU q hq h hd A B start a b i j
    hi hj ha hmB hmC hcard hAfull hBfull u v hu hv huv hui hvi⟩

end Erdos335.Loeb

end
