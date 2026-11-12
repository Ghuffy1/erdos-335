import Erdos335.LoebBohrResidueProfiles
import Erdos335.LoebProfileBounds

/-!
# Refined residue profiles of both members of an internal Bohr pair
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance bohrPairProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem InternalBohrPairData.residue_profiles
    {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ atTop} {q : ℕ → ℕ+}
    {A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))}
    (b : InternalBohrPairData U hU q A B) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (b.modulus : ℕ) ∣ (h : ℕ)) :
    (∀ r, loebResidueProfile U hU q h A r =
      if naturalCyclicProjection h b.modulus r = finiteQuotient U b.residue b.left_anchor
        then b.left_length else 0) ∧
    (∀ r, loebResidueProfile U hU q h B r =
      if naturalCyclicProjection h b.modulus r = finiteQuotient U b.residue b.right_anchor
        then b.right_length else 0) := by
  have hmd : ∀ᶠ n in U, (b.modulus : ℕ) ∣ (q n : ℕ) := hd.mono fun n hn => dvd_trans hmh hn
  have hquotient : finiteQuotient U b.residue =
      finiteQuotient U (fun n => naturalCyclicProjection (q n) b.modulus) := by
    apply finiteQuotient_eq_of_eventually_natural
    · exact b.natural_residue.mono fun n hn => hn.2
    · exact hmd.mono fun n hn t => naturalCyclicProjection_natCast (q n) b.modulus hn t
  have profile (C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
      (anchor : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      (start : AddCircle (1 : ℝ)) (length : ℝ) (h0 : 0 ≤ length) (h1 : length ≤ 1)
      (hmodel : C =ᵐ[loebMeasure U hU]
        internalBohrCoset U q b.modulus b.residue b.character anchor start length) (r : ZMod (h : ℕ)) :
      loebResidueProfile U hU q h C r =
        if naturalCyclicProjection h b.modulus r = finiteQuotient U b.residue anchor then length else 0 := by
    rw [loebResidueProfile_eq_of_ae U hU q h C _ hmodel]
    unfold internalBohrCoset
    rw [hquotient]
    exact loeb_natural_bohr_residue_profile U hU q b.modulus h hd hmh b.character
      b.character_surjective anchor start length h0 h1 r
  constructor
  · exact fun r => profile A b.left_anchor b.left_start b.left_length b.left_positive.le
      (by linarith [b.length_sum_lt_one, b.right_positive]) b.left_model r
  · exact fun r => profile B b.right_anchor b.right_start b.right_length b.right_positive.le
      (by linarith [b.length_sum_lt_one, b.left_positive]) b.right_model r

end Erdos335.Loeb

end
