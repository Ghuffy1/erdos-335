import Erdos335.WindowResidueRefinement
import Erdos335.LoebWindowTranslations
import Erdos335.LoebNullActivePeriods

/-!
# Fixed integer translations of actual window fibers
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance actualFiberTranslationsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

def actualWindowFiber
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+) (A : Set ℕ) (start : ℕ → ℕ)
    (r : ZMod (h : ℕ)) : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ∩
    windowResidueMap U q h start ⁻¹' {r}

theorem measurable_actualWindowFiber
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+) (A : Set ℕ) (start : ℕ → ℕ)
    (r : ZMod (h : ℕ)) : MeasurableSet (actualWindowFiber U q h A start r) := by
  unfold actualWindowFiber
  rw [windowResidueMap_fiber]
  rw [finiteQuotient_preimage_internal]
  exact (measurable_internalSet U _).inter (measurable_internalSet U _)

theorem windowResidueMap_nat_translate
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (start : ℕ → ℕ) (u : ℕ)
    (x : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    windowResidueMap U q h start
      (productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) + x) =
      windowResidueMap U q h start x + (u : ZMod (h : ℕ)) := by
  have ht := finiteQuotient_natCast_of_eventually U q h
    (fun n => naturalCyclicProjection (q n) h)
    (hd.mono fun n hn v => naturalCyclicProjection_natCast (q n) h hn v) u
  unfold windowResidueMap
  rw [map_add, ht]
  abel

theorem actual_window_fiber_translate_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (u : ℕ) (hu : u ∈ A) (j : ZMod (h : ℕ)) :
    productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
      actualWindowFiber U q h B start j ≤ᵐ[loebMeasure U hU]
        actualWindowFiber U q h (A + B) start ((u : ZMod (h : ℕ)) + j) := by
  have htrans := loeb_cyclic_window_literal_translate_ae U hU q hq B A start u hu
  filter_upwards [htrans] with x hx
  rintro ⟨y, hy, rfl⟩
  refine ⟨?_, ?_⟩
  · have hc := hx ⟨y, hy.1, rfl⟩
    simpa only [add_comm B A] using hc
  · change windowResidueMap U q h start
        (productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) + y) = _
    rw [windowResidueMap_nat_translate U q h hd start u y,
      show windowResidueMap U q h start y = j from hy.2, add_comm]

theorem actual_window_fiber_equal_translate
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (u : ℕ) (hu : u ∈ A) (j : ZMod (h : ℕ))
    (hmass : loebMeasure U hU (actualWindowFiber U q h B start j) =
      loebMeasure U hU (actualWindowFiber U q h (A + B) start ((u : ZMod (h : ℕ)) + j))) :
    productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
      actualWindowFiber U q h B start j =ᵐ[loebMeasure U hU]
        actualWindowFiber U q h (A + B) start ((u : ZMod (h : ℕ)) + j) := by
  letI : IsProbabilityMeasure (loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU) :=
    isProbabilityMeasure_loebMeasure U hU
  apply ae_eq_of_ae_subset_of_measure_ge
    (actual_window_fiber_translate_subset U hU q hq h hd A B start u hu j)
  · exact hmass.symm.le.trans_eq (loebMeasure_image_add_left U hU _ _).symm
  · exact (measurable_loeb_translate U hU _
      (measurable_actualWindowFiber U q h B start j) _).nullMeasurableSet
  · exact measure_ne_top (loebMeasure U hU) _

theorem actual_window_fiber_difference_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (u v : ℕ) (hu : u ∈ A) (hv : v ∈ A)
    (i j : ZMod (h : ℕ)) (hui : (u : ZMod (h : ℕ)) = i) (hvi : (v : ZMod (h : ℕ)) = i)
    (hmass : loebMeasure U hU (actualWindowFiber U q h B start j) =
      loebMeasure U hU (actualWindowFiber U q h (A + B) start (i + j))) :
    (productProjection (U : Filter ℕ) (fun n => (v : ZMod (q n : ℕ))) -
      productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ)))) +ᵥ
        actualWindowFiber U q h B start j =ᵐ[loebMeasure U hU]
          actualWindowFiber U q h B start j := by
  have huEq := actual_window_fiber_equal_translate U hU q hq h hd A B start u hu j
    (by simpa only [hui] using hmass)
  have hvEq := actual_window_fiber_equal_translate U hU q hq h hd A B start v hv j
    (by simpa only [hvi] using hmass)
  rw [hui] at huEq
  rw [hvi] at hvEq
  exact loeb_equal_translate_difference_period U hU q _ _ _ _ hvEq huEq

end Erdos335.Loeb

end
