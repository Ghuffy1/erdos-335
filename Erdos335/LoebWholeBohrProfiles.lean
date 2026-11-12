import Erdos335.LoebBohrSumModel
import Erdos335.LoebBohrPairSwap
import Erdos335.WindowResidueRefinement

/-!
# Physical profiles for a whole internal Bohr pair
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance wholeBohrProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem whole_bohr_right_physical_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (d : InternalBohrPairData U hU q A B) (X : Set ℕ) (start : ℕ → ℕ)
    (hmodel : B =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow X (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (d.modulus : ℕ) ∣ (h : ℕ))
    (r : ZMod (h : ℕ)) :
    actualWindowProfile U hU q h X start r =
      if naturalCyclicProjection h d.modulus r = finiteQuotient U d.residue d.right_anchor +
          finiteValue U (fun n => (start n : ZMod (d.modulus : ℕ)))
        then d.right_length else 0 := by
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  let z₀ := finiteValue U (fun n => (start n : ZMod (d.modulus : ℕ)))
  let π := naturalCyclicProjection h d.modulus
  have hphase : π z = z₀ := by
    have hp := windowResidueMap_refinement U q h d.modulus start hd hmh 0
    simpa only [windowResidueMap, map_zero, zero_add] using hp
  change loebResidueProfile U hU q h _ (r - z) = _
  rw [← loebResidueProfile_eq_of_ae U hU q h B _ hmodel]
  have hp := (d.residue_profiles h hd hmh).2 (r - z)
  change loebResidueProfile U hU q h B (r - z) =
    (if π (r - z) = finiteQuotient U d.residue d.right_anchor then d.right_length else 0) at hp
  rw [map_sub, hphase] at hp
  simpa only [sub_eq_iff_eq_add, internalBohrCoset] using hp

theorem whole_bohr_left_physical_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (d : InternalBohrPairData U hU q A B) (X : Set ℕ) (start : ℕ → ℕ)
    (hmodel : A =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow X (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (d.modulus : ℕ) ∣ (h : ℕ))
    (r : ZMod (h : ℕ)) :
    actualWindowProfile U hU q h X start r =
      if naturalCyclicProjection h d.modulus r = finiteQuotient U d.residue d.left_anchor +
          finiteValue U (fun n => (start n : ZMod (d.modulus : ℕ)))
        then d.left_length else 0 :=
  whole_bohr_right_physical_profile U hU q B A d.swap X start hmodel h hd hmh r

theorem whole_bohr_output_physical_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (d : InternalBohrPairData U hU q A B)
    (hSm : MeasurableSet (A + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (C : Set ℕ) (start : ℕ → ℕ)
    (hmodel : A + B =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow C (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (d.modulus : ℕ) ∣ (h : ℕ))
    (r : ZMod (h : ℕ)) :
    actualWindowProfile U hU q h C start r =
      if naturalCyclicProjection h d.modulus r = finiteQuotient U d.residue (d.left_anchor + d.right_anchor) +
          finiteValue U (fun n => (start n : ZMod (d.modulus : ℕ)))
        then d.left_length + d.right_length else 0 := by
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  let z₀ := finiteValue U (fun n => (start n : ZMod (d.modulus : ℕ)))
  let π := naturalCyclicProjection h d.modulus
  have hphase : π z = z₀ := by
    have hp := windowResidueMap_refinement U q h d.modulus start hd hmh 0
    simpa only [windowResidueMap, map_zero, zero_add] using hp
  have hmod : ∀ᶠ n in U, (d.modulus : ℕ) ∣ (q n : ℕ) := hd.mono fun n hn => dvd_trans hmh hn
  have hquotient := finiteQuotient_eq_of_eventually_natural U q d.modulus d.residue
    (fun n => naturalCyclicProjection (q n) d.modulus)
    (d.natural_residue.mono fun n hn => hn.2)
    (hmod.mono fun n hn v => naturalCyclicProjection_natCast (q n) d.modulus hn v)
  have hsum := d.sum_model hSm hfull
  have hcoset := hmodel.symm.trans hsum
  change loebResidueProfile U hU q h _ (r - z) = _
  rw [loebResidueProfile_eq_of_ae U hU q h _ _ hcoset]
  have hp := loeb_natural_bohr_residue_profile U hU q d.modulus h hd hmh d.character
    d.character_surjective (d.left_anchor + d.right_anchor) (d.left_start + d.right_start)
    (d.left_length + d.right_length) (add_nonneg d.left_positive.le d.right_positive.le)
    d.length_sum_lt_one.le (r - z)
  simp only [internalBohrCoset, ← hquotient] at hp
  change loebResidueProfile U hU q h _ (r - z) =
    (if π (r - z) = finiteQuotient U d.residue (d.left_anchor + d.right_anchor)
      then d.left_length + d.right_length else 0) at hp
  rw [map_sub, hphase] at hp
  simpa only [sub_eq_iff_eq_add, internalBohrCoset] using hp

end Erdos335.Loeb

end
