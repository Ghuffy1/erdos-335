import Erdos335.LoebWindowMaskBounds
import Erdos335.LoebLiteralResidues
import Erdos335.ResidueCapacityMasks
import Erdos335.FiniteProfileLowerBound

/-!
# Positive profiles and literal residue capacities
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped ENNReal BigOperators

noncomputable section

namespace Erdos335.Loeb

local instance profileCapacityLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_window_profile_ge_total_sub_card
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (a : ℝ)
    (hmass : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (r : ZMod (h : ℕ)) (hr : r ∈ residues (h : ℕ) A) :
    ((h : ℕ) : ℝ) * a - ((residues (h : ℕ) A).card - 1) ≤
      actualWindowProfile U hU q h A start r := by
  have hsum : (∑ v, actualWindowProfile U hU q h A start v) = ((h : ℕ) : ℝ) * a := by
    have hs := sum_shifted_loebResidueProfile U hU q h
      (internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
      (finiteValue U (fun n => (start n : ZMod (h : ℕ))))
    simpa only [actualWindowProfile, hmass] using hs
  have hb := FiniteProfiles.coordinate_ge_total_sub_card (residues (h : ℕ) A)
    (actualWindowProfile U hU q h A start)
    (actual_window_profile_zero_outside_residues U hU q h hd A start)
    (fun v => loebResidueProfile_le_one U hU q h hd _ _) r hr
  rwa [hsum] at hb

theorem actual_window_capacity_ge_of_positive_refinements
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (m : ℕ+) (R : Finset (ZMod (m : ℕ)))
    (hpositive : ∀ h : ℕ+, (m : ℕ) ∣ (h : ℕ) → ∀ r : ZMod (h : ℕ),
      naturalCyclicProjection h m r ∈ R → 0 < actualWindowProfile U hU q h A start r) :
    ∀ k : ℕ+, (R.card : ℝ) / (m : ℕ) ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) := by
  have hcap (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) :
      (R.card : ℝ) / (m : ℕ) ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
    apply residue_capacity_ge_of_full_coarse_mask A m h hmh R
    intro r hr
    by_contra hn
    exact (hpositive h hmh r hr).ne' (actual_window_profile_zero_outside_residues U hU q h (hdiv h) A start r hn)
  intro k
  exact (hcap (m * k) ⟨k, rfl⟩).trans
    (residue_capacity_mono_of_dvd A k (m * k) ⟨m, Nat.mul_comm _ _⟩)

theorem literal_prefix_profile_zero_outside_residues
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ℕ) (E : ℕ → Set ℕ)
    (hEsub : ∀ᶠ n in U, E n ⊆ A) (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (r : ZMod (h : ℕ)) (hr : r ∉ residues (h : ℕ) A) :
    loebResidueProfile U hU q h
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) r = 0 := by
  have himage := finiteQuotient_image_of_literal_exhaustion U q A E hEsub hexhaust h
    (fun n => naturalCyclicProjection (q n) h)
    (hd.mono fun n hn a => naturalCyclicProjection_natCast (q n) h hn a)
  apply loebResidueProfile_zero_of_subset U hU q h _ (residues (h : ℕ) A) _ r hr
  rw [← himage]
  exact subset_preimage_image _ _

theorem literal_prefix_capacity_ge_of_positive_refinements
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (E : ℕ → Set ℕ)
    (hEsub : ∀ᶠ n in U, E n ⊆ A) (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (m : ℕ+) (R : Finset (ZMod (m : ℕ)))
    (hpositive : ∀ h : ℕ+, (m : ℕ) ∣ (h : ℕ) → ∀ r : ZMod (h : ℕ),
      naturalCyclicProjection h m r ∈ R → 0 < loebResidueProfile U hU q h
        (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) r) :
    ∀ k : ℕ+, (R.card : ℝ) / (m : ℕ) ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) := by
  have hcap (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) :
      (R.card : ℝ) / (m : ℕ) ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
    apply residue_capacity_ge_of_full_coarse_mask A m h hmh R
    intro r hr
    by_contra hn
    exact (hpositive h hmh r hr).ne'
      (literal_prefix_profile_zero_outside_residues U hU q A E hEsub hexhaust h (hdiv h) r hn)
  intro k
  exact (hcap (m * k) ⟨k, rfl⟩).trans
    (residue_capacity_mono_of_dvd A k (m * k) ⟨m, Nat.mul_comm _ _⟩)

end Erdos335.Loeb

end
