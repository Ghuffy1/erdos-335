import Erdos335.LoebQuasiBohrFiniteProfiles
import Erdos335.WindowResidueRefinement

/-!
# Physical input residues of a positive quasi-periodic terminal
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal Classical

noncomputable section

namespace Erdos335.Loeb

local instance physicalBohrInputsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_physical_bohr_right_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (b : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U b.residue).ker)
    (X : Set ℕ) (start : ℕ → ℕ)
    (hmodel : B =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow X (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (R : Finset (ZMod (b.modulus : ℕ)))
    (hR : (finiteQuotient U b.residue) '' B = (R : Set _))
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (b.modulus : ℕ) ∣ (h : ℕ))
    (r : ZMod (h : ℕ)) :
    actualWindowProfile U hU q h X start r =
      if naturalCyclicProjection h b.modulus r =
          finiteQuotient U b.residue b.right_anchor +
            finiteValue U (fun n => (start n : ZMod (b.modulus : ℕ)))
        then b.right_length
      else if naturalCyclicProjection h b.modulus r ∈
          R.image (fun v => v + finiteValue U (fun n => (start n : ZMod (b.modulus : ℕ))))
        then 1 else 0 := by
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  let z₀ := finiteValue U (fun n => (start n : ZMod (b.modulus : ℕ)))
  let π := naturalCyclicProjection h b.modulus
  have hphase : π z = z₀ := by
    have hp := windowResidueMap_refinement U q h b.modulus start hd hmh 0
    simpa only [windowResidueMap, map_zero, zero_add] using hp
  change loebResidueProfile U hU q h _ (r - z) = _
  rw [← loebResidueProfile_eq_of_ae U hU q h B _ hmodel]
  have hp := loeb_quasiBohr_right_residue_profile U hU q A B p b hperiod h hd hmh (r - z)
  change loebResidueProfile U hU q h B (r - z) =
    (if π (r - z) = finiteQuotient U b.residue b.right_anchor then b.right_length
      else if π (r - z) ∈ (finiteQuotient U b.residue) '' B then 1 else 0) at hp
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

theorem loeb_physical_bohr_left_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (b : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U b.residue).ker)
    (X : Set ℕ) (start : ℕ → ℕ)
    (hmodel : A =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow X (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (R : Finset (ZMod (b.modulus : ℕ)))
    (hR : (finiteQuotient U b.residue) '' A = (R : Set _))
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (b.modulus : ℕ) ∣ (h : ℕ))
    (r : ZMod (h : ℕ)) :
    actualWindowProfile U hU q h X start r =
      if naturalCyclicProjection h b.modulus r =
          finiteQuotient U b.residue b.left_anchor +
            finiteValue U (fun n => (start n : ZMod (b.modulus : ℕ)))
        then b.left_length
      else if naturalCyclicProjection h b.modulus r ∈
          R.image (fun v => v + finiteValue U (fun n => (start n : ZMod (b.modulus : ℕ))))
        then 1 else 0 :=
  loeb_physical_bohr_right_profile U hU q B A p.swap b.swap hperiod X start hmodel R hR h hd hmh r

end Erdos335.Loeb

end
