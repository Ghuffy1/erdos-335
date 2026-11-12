import Erdos335.LoebActiveFiberPeriods

/-!
# Actual integer differences give periods in a local null frame
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance nullFramePeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem null_frame_integer_difference_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (i j : ZMod (h : ℕ))
    (hi : i ∈ residues (h : ℕ) A) (hj : j ∈ residues (h : ℕ) B)
    (ha : a = (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ))
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hcard : (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
      (residues (h : ℕ) A).card + (residues (h : ℕ) B).card)
    (hAfull : ∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1)
    (hBfull : ∀ r ∈ (residues (h : ℕ) B).erase j, actualWindowProfile U hU q h B start r = 1)
    (u v : ℕ) (hu : u ∈ A) (hv : v ∈ A) (huv : u < v)
    (hui : (u : ZMod (h : ℕ)) = i) (hvi : (v : ZMod (h : ℕ)) = i) :
    let t := productProjection (U : Filter ℕ) (fun n => ((v - u : ℕ) : ZMod (q n : ℕ)))
    t +ᵥ internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU]
        internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ∧
    t +ᵥ internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU]
        internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  dsimp only
  let point := fun w : ℕ => productProjection (U : Filter ℕ) (fun n => (w : ZMod (q n : ℕ)))
  let t := point v - point u
  have hmass := null_frame_active_measures_equal U hU q hq h hd A B start a b i j hi hj ha hmB hmC
    hcard hAfull hBfull
  have hBactive := actual_window_fiber_difference_period U hU q hq h hd A B start u v hu hv i j hui hvi hmass
  have huEq := actual_window_fiber_equal_translate U hU q hq h hd A B start u hu j
    (by simpa only [hui] using hmass)
  rw [hui] at huEq
  have ht : finiteQuotient U (fun n => naturalCyclicProjection (q n) h) t = 0 := by
    have hu' := finiteQuotient_natCast_of_eventually U q h
      (fun n => naturalCyclicProjection (q n) h)
      (hd.mono fun n hn w => naturalCyclicProjection_natCast (q n) h hn w) u
    have hv' := finiteQuotient_natCast_of_eventually U q h
      (fun n => naturalCyclicProjection (q n) h)
      (hd.mono fun n hn w => naturalCyclicProjection_natCast (q n) h hn w) v
    dsimp only [t]
    rw [map_sub, hv', hu', hvi, hui, sub_self]
  have hCactive : t +ᵥ actualWindowFiber U q h (A + B) start (i + j) =ᵐ[loebMeasure U hU]
      actualWindowFiber U q h (A + B) start (i + j) := by
    have hmove := loeb_vadd_congr_ae U hU _ _ t huEq.symm
    have hcomm : t +ᵥ (point u +ᵥ actualWindowFiber U q h B start j) =
        point u +ᵥ (t +ᵥ actualWindowFiber U q h B start j) := by
      rw [vadd_vadd, vadd_vadd, add_comm t]
    rw [hcomm] at hmove
    exact hmove.trans ((loeb_vadd_congr_ae U hU _ _ (point u) hBactive).trans huEq)
  have hBperiod := actual_window_period_of_active_fiber U hU q h hd B start j hBfull t ht hBactive
  have hCfull := actual_window_nonactive_output_full U hU q hq h hd A B start i j hAfull hBfull
  have hCperiod := actual_window_period_of_active_fiber U hU q h hd (A + B) start (i + j)
    (by simpa only [residues_add] using hCfull) t ht hCactive
  have hpoints : t = productProjection (U : Filter ℕ) (fun n => ((v - u : ℕ) : ZMod (q n : ℕ))) := by
    change productProjection (U : Filter ℕ) (fun n => (v : ZMod (q n : ℕ)) - (u : ZMod (q n : ℕ))) = _
    congr 1
    funext n
    exact (Nat.cast_sub huv.le).symm
  rw [hpoints] at hBperiod hCperiod
  exact ⟨hBperiod, hCperiod⟩

end Erdos335.Loeb

end
