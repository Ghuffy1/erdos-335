import Erdos335.LoebQuasiBohrOutputProfiles
import Erdos335.WindowResidueRefinement

/-!
# Physical output residues of a positive quasi-periodic terminal
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal Classical

noncomputable section

namespace Erdos335.Loeb

local instance physicalBohrOutputLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_physical_bohr_output_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hSm : MeasurableSet (A + B))
    (b : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U b.residue).ker)
    (C : Set ℕ) (start : ℕ → ℕ)
    (hmodel : A + B =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow C (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (R : Finset (ZMod (b.modulus : ℕ)))
    (hR : (finiteQuotient U b.residue) '' (A + B) = (R : Set _))
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (b.modulus : ℕ) ∣ (h : ℕ))
    (r : ZMod (h : ℕ)) :
    actualWindowProfile U hU q h C start r =
      if naturalCyclicProjection h b.modulus r =
          finiteQuotient U b.residue (b.left_anchor + b.right_anchor) +
            finiteValue U (fun n => (start n : ZMod (b.modulus : ℕ)))
        then b.left_length + b.right_length
      else if naturalCyclicProjection h b.modulus r ∈
          R.image (fun v => v + finiteValue U (fun n => (start n : ZMod (b.modulus : ℕ))))
        then 1 else 0 := by
  classical
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  let z₀ := finiteValue U (fun n => (start n : ZMod (b.modulus : ℕ)))
  let π := naturalCyclicProjection h b.modulus
  have hphase : π z = z₀ := by
    have hp := windowResidueMap_refinement U q h b.modulus start hd hmh 0
    simpa only [windowResidueMap, map_zero, zero_add] using hp
  have hphysical : actualWindowProfile U hU q h C start r =
      loebResidueProfile U hU q h (A + B) (r - z) :=
    (loebResidueProfile_eq_of_ae U hU q h (A + B) _ hmodel (r - z)).symm
  rw [hphysical]
  have hp := loeb_quasiBohr_output_residue_profile U hU q A B p hSm b hperiod h hd hmh (r - z)
  change loebResidueProfile U hU q h (A + B) (r - z) =
    (if π (r - z) = finiteQuotient U b.residue (b.left_anchor + b.right_anchor)
      then b.left_length + b.right_length else if π (r - z) ∈ (finiteQuotient U b.residue) '' (A + B)
      then 1 else 0) at hp
  rw [map_sub, hphase, hR] at hp
  have hmem : π r - z₀ ∈ R ↔ π r ∈ R.image (fun v => v + z₀) := by
    constructor
    · intro hr
      exact Finset.mem_image.mpr ⟨π r - z₀, hr, sub_add_cancel _ _⟩
    · intro hr
      obtain ⟨v, hv, hvr⟩ := Finset.mem_image.mp hr
      rw [← hvr, add_sub_cancel_right]
      exact hv
  simpa only [sub_eq_iff_eq_add, Finset.mem_coe, hmem] using hp

end Erdos335.Loeb

end
