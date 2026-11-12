import Erdos335.LoebQuasiOffActive
import Erdos335.WindowResidueRefinement

/-!
# Physical nonexceptional profiles of a quasi-periodic model
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance physicalQuasiOffLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_physical_quasi_off_active
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H W)
    (k : ℕ+) (hker : (finiteQuotient U (fun n => naturalCyclicProjection (q n) k)).ker = H)
    (C : Set ℕ) (start : ℕ → ℕ)
    (hmodel : W =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow C (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (n : ℕ+) (hd : ∀ᶠ s in U, (n : ℕ) ∣ (q s : ℕ)) (hkn : (k : ℕ) ∣ (n : ℕ))
    (r : ZMod (n : ℕ))
    (hr : naturalCyclicProjection n k r ≠
      finiteQuotient U (fun s => naturalCyclicProjection (q s) k) p.anchor +
        finiteValue U (fun s => (start s : ZMod (k : ℕ)))) :
    actualWindowProfile U hU q n C start r = 0 ∨ actualWindowProfile U hU q n C start r = 1 := by
  let f := finiteQuotient U (fun s => naturalCyclicProjection (q s) k)
  let π := naturalCyclicProjection n k
  let z := finiteValue U (fun s => (start s : ZMod (n : ℕ)))
  let z₀ := finiteValue U (fun s => (start s : ZMod (k : ℕ)))
  have hphase : π z = z₀ := by
    have hp := windowResidueMap_refinement U q n k start hd hkn 0
    simpa only [windowResidueMap, map_zero, zero_add] using hp
  have hcomp (x : (U : Filter ℕ).Product (fun s => ZMod (q s : ℕ))) :
      π (finiteQuotient U (fun s => naturalCyclicProjection (q s) n) x) = f x := by
    exact congrArg (fun g => g x) (finiteQuotient_natural_refinement U q n k hd hkn)
  have hr' : π (r - z) ≠ f p.anchor := by
    rw [map_sub, hphase]
    intro heq
    exact hr ((sub_eq_iff_eq_add).mp heq)
  have hprofile : actualWindowProfile U hU q n C start r = loebResidueProfile U hU q n W (r - z) :=
    (loebResidueProfile_eq_of_ae U hU q n W _ hmodel (r - z)).symm
  rw [hprofile]
  exact loeb_quasiPeriodic_refined_off_active U hU q W H p f hker n hd π hcomp (r - z) hr'

end Erdos335.Loeb

end
