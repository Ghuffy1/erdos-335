import Erdos335.LoebCyclicModelContainment
import Erdos335.LoebActualResidues

/-!
# Literal translations between actual window profiles
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance windowTranslationsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_cyclic_window_literal_translate_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun s => (q s : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (b : ℕ) (hb : b ∈ B) :
    productProjection (U : Filter ℕ) (fun s => (b : ZMod (q s : ℕ))) +ᵥ
        internalSet U (fun s => (cyclicWindow A (start s) (q s : ℕ) : Set (ZMod (q s : ℕ))))
      ≤ᵐ[loebMeasure U hU]
        internalSet U (fun s => (cyclicWindow (A + B) (start s) (q s : ℕ) : Set (ZMod (q s : ℕ)))) := by
  classical
  have hspill : Tendsto (fun s => (((cyclicWindow A (start s) (q s : ℕ) + {(b : ZMod (q s : ℕ))}) \
      cyclicWindow (A + B) (start s) (q s : ℕ)).card : ℝ) / (q s : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_
      ((tendsto_const_div_atTop_nhds_zero_nat (b : ℝ)).comp hq)
    filter_upwards [hq.eventually (eventually_gt_atTop b)] with s hs
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast fixed_shift_window_error_le A B (start s) (q s : ℕ) b hb hs) (by positivity)
  have hsum := loeb_cyclic_sum_ae_subset U hU q
    (fun s => cyclicWindow A (start s) (q s : ℕ))
    (fun s => {(b : ZMod (q s : ℕ))})
    (fun s => cyclicWindow (A + B) (start s) (q s : ℕ)) hspill
  simp only [Finset.coe_singleton, internalSet_singleton] at hsum
  rw [add_comm, Set.singleton_add] at hsum
  exact hsum

theorem actual_window_profile_translate_le
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun s => (q s : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ s in U, (h : ℕ) ∣ (q s : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (b : ℕ) (hb : b ∈ B) (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h
      (internalSet U (fun s => (cyclicWindow A (start s) (q s : ℕ) : Set (ZMod (q s : ℕ)))))
      (r - finiteValue U (fun s => (start s : ZMod (h : ℕ)))) ≤
    loebResidueProfile U hU q h
      (internalSet U (fun s => (cyclicWindow (A + B) (start s) (q s : ℕ) : Set (ZMod (q s : ℕ)))))
      (r + (b : ZMod (h : ℕ)) - finiteValue U (fun s => (start s : ZMod (h : ℕ)))) := by
  have ht := finiteQuotient_natCast_of_eventually U q h
    (fun s => naturalCyclicProjection (q s) h)
    (hd.mono fun s hs n => naturalCyclicProjection_natCast (q s) h hs n) b
  have hbound := loebResidueProfile_translate_le U hU q h _ _
    (productProjection (U : Filter ℕ) (fun s => (b : ZMod (q s : ℕ))))
    (loeb_cyclic_window_literal_translate_ae U hU q hq A B start b hb)
    (r - finiteValue U (fun s => (start s : ZMod (h : ℕ))))
  rw [ht] at hbound
  convert hbound using 1 <;> congr 1 <;> abel

end Erdos335.Loeb

end
