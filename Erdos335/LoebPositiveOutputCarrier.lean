import Erdos335.LoebProfileCapacity

/-!
# Literal output carriers determined by positive window profiles
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance positiveOutputCarrierLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_output_literal_carrier
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (R : Finset (ZMod (h : ℕ)))
    (hpartner : ∀ t ∈ residues (h : ℕ) B, 0 < actualWindowProfile U hU q h B start t)
    (hzero : ∀ r ∉ R, actualWindowProfile U hU q h (A + B) start r = 0)
    (hpositive : ∀ r ∈ R, 0 < actualWindowProfile U hU q h (A + B) start r) :
    residues (h : ℕ) (A + B) = R := by
  apply Finset.Subset.antisymm
  · intro r hr
    rw [residues_add] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hr
    obtain ⟨n, hn, hnu⟩ := mem_residues.mp hu
    have hle := actual_window_profile_translate_le U hU q hq h hd B A start n hn v
    change actualWindowProfile U hU q h B start v ≤
      actualWindowProfile U hU q h (B + A) start (v + (n : ZMod (h : ℕ))) at hle
    have hle' : actualWindowProfile U hU q h B start v ≤
        actualWindowProfile U hU q h (A + B) start (u + v) := by
      simpa only [hnu, add_comm B A, add_comm v u] using hle
    by_contra hout
    rw [hzero (u + v) hout] at hle'
    exact not_le_of_gt (hpartner v hv) hle'
  · intro r hr
    by_contra hout
    exact (hpositive r hr).ne'
      (actual_window_profile_zero_outside_residues U hU q h hd (A + B) start r hout)

theorem gamma_eq_of_positive_window_refinements
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (m : ℕ+) (R : Finset (ZMod (m : ℕ)))
    (hcarrier : residues (m : ℕ) (A + B) = R)
    (hpositive : ∀ h : ℕ+, (m : ℕ) ∣ (h : ℕ) → ∀ r : ZMod (h : ℕ),
      naturalCyclicProjection h m r ∈ R → 0 < actualWindowProfile U hU q h (A + B) start r) :
    gamma A B = (R.card : ℝ) / (m : ℕ) := by
  apply le_antisymm
  · have hupper := gamma_le_modularCapacity A B m
    change gamma A B ≤ ((residues (m : ℕ) A + residues (m : ℕ) B).card : ℝ) / (m : ℕ) at hupper
    rwa [← residues_add, hcarrier] at hupper
  · apply le_ciInf
    intro k
    have hlower := actual_window_capacity_ge_of_positive_refinements U hU q hdiv
      (A + B) start m R hpositive k
    simpa only [modularCapacity, residues_add] using hlower

end Erdos335.Loeb

end
