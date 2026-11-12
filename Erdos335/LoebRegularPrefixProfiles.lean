import Erdos335.LoebRegularPrefixWindow
import Erdos335.LoebPeriodicWindowProfiles

/-!
# Matching the physical window and literal prefix residue profiles
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance regularPrefixProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loebResidueProfile_vadd
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h (t +ᵥ S)
      (r + finiteQuotient U (fun n => naturalCyclicProjection (q n) h) t) = loebResidueProfile U hU q h S r := by
  have hleft := loebResidueProfile_translate_le U hU q h S (t +ᵥ S) t
    (Filter.Eventually.of_forall fun x hx => hx) r
  have hback : (-t) +ᵥ (t +ᵥ S) ≤ᵐ[loebMeasure U hU] S := by
    simpa only [neg_vadd_vadd] using (show S ≤ᵐ[loebMeasure U hU] S from
      Filter.Eventually.of_forall fun x hx => hx)
  have hright := loebResidueProfile_translate_le U hU q h (t +ᵥ S) S (-t) hback
    (r + finiteQuotient U (fun n => naturalCyclicProjection (q n) h) t)
  rw [map_neg, add_neg_cancel_right] at hright
  exact le_antisymm hright hleft

theorem loeb_regular_prefix_profile_eq_window
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (E : ℕ → Set ℕ) (start : ℕ → ℕ)
    (hEA : ∀ᶠ n in U, E n ⊆ A) (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (a : ℝ)
    (hmE : (loebMeasure U hU (internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = a)
    (hmW : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε)
    (h : ℕ+) (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) r =
      actualWindowProfile U hU q h A start r := by
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let W := internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  let v := productProjection (U : Filter ℕ) (fun n => (start n : ZMod (q n : ℕ)))
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  have hAE := loeb_regular_prefix_window_agreement U hU q hdiv A E start hEA hexhaust a hmE hmW happrox
  have hv : finiteQuotient U (fun n => naturalCyclicProjection (q n) h) v = z := by
    change finiteValue U (fun n => naturalCyclicProjection (q n) h (start n : ZMod (q n : ℕ))) = _
    apply finiteValue_congr
    exact (hdiv h).mono fun n hn => naturalCyclicProjection_natCast (q n) h hn (start n)
  have ht := loebResidueProfile_vadd U hU q h W v (r - z)
  rw [hv, sub_add_cancel] at ht
  exact (loebResidueProfile_eq_of_ae U hU q h P (v +ᵥ W) hAE r).trans ht

end Erdos335.Loeb

end
