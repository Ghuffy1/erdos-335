import Erdos335.ApproximateDensityCovers
import Erdos335.LoebWindowMaskBounds
import Erdos335.ResidueCapacityRefinement
import Erdos335.LoebPeriodicWindowInputs

/-!
# A periodic regular window determines an ordinary periodic template
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance regularGlobalMaskLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_window_profile_full_of_coarse_mask
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (m : ℕ) ∣ (h : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (R : Finset (ZMod (m : ℕ)))
    (hR : windowResidueMap U q m start ⁻¹' (R : Set _) ≤ᵐ[loebMeasure U hU]
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (r : ZMod (h : ℕ)) (hr : naturalCyclicProjection h m r ∈ R) :
    actualWindowProfile U hU q h A start r = 1 := by
  apply loebResidueProfile_one_of_fiber_ae_subset U hU q h hd
  have hsub : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹'
        {r - finiteValue U (fun n => (start n : ZMod (h : ℕ)))} ⊆
      windowResidueMap U q m start ⁻¹' (R : Set _) := by
    rw [← windowResidueMap_fiber]
    intro x hx
    change windowResidueMap U q m start x ∈ R
    rw [← windowResidueMap_refinement U q h m start hd hmh x]
    change windowResidueMap U q h start x = r at hx
    rw [hx]
    exact hr
  exact hsub.eventuallySubset.trans hR

theorem periodic_mask_subset_residue_cover_of_window
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (m : ℕ) ∣ (h : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (R : Finset (ZMod (m : ℕ)))
    (hR : windowResidueMap U q m start ⁻¹' (R : Set _) ≤ᵐ[loebMeasure U hU]
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    periodicSet R ⊆ periodicSet (residues (h : ℕ) A) := by
  rintro n ⟨hn, hnr⟩
  refine ⟨hn, ?_⟩
  have hr : naturalCyclicProjection h m (n : ZMod (h : ℕ)) ∈ R := by
    rw [naturalCyclicProjection_natCast h m hmh]
    exact hnr
  have hfull := actual_window_profile_full_of_coarse_mask U hU q m h hd hmh A start R hR _ hr
  by_contra hnot
  have hzero := actual_window_profile_zero_outside_residues U hU q h hd A start _ hnot
  change actualWindowProfile U hU q h A start (n : ZMod (h : ℕ)) = 0 at hzero
  rw [hzero] at hfull
  exact zero_ne_one hfull

theorem loeb_regular_window_global_mask
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (a : ℝ) (hA : A ⊆ Set.Ioi 0)
    (hdA : HasDensity A a)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε)
    (m : ℕ+) (R : Finset (ZMod (m : ℕ)))
    (hR : internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU] windowResidueMap U q m start ⁻¹' (R : Set _)) :
    DensityEquivalent A (periodicSet R) := by
  have hmass : (R.card : ℝ) / (m : ℕ) = a := by
    have heq := (congrArg ENNReal.toReal (measure_congr hR)).symm.trans hmA
    rw [loebMeasure_windowResidueMap_preimage U hU q m (hdiv m),
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at heq
    exact heq
  have hdR : HasDensity (periodicSet R) a := by
    simpa only [hmass] using hasDensity_periodicSet R
  apply densityEquivalent_of_common_approximate_covers A (periodicSet R) a hdA hdR
  intro ε hε
  obtain ⟨h, hmh, hh⟩ := residue_capacity_approximants_at_multiples A a happrox m ε hε
  refine ⟨periodicSet (residues (h : ℕ) A),
    ((residues (h : ℕ) A).card : ℝ) / (h : ℕ), subset_periodic_residues (h : ℕ) A hA,
    periodic_mask_subset_residue_cover_of_window U hU q m h (hdiv h) hmh A start R hR.symm.le,
    hasDensity_periodicSet _, hh⟩

theorem loeb_regular_natural_window_global_mask
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (a : ℝ) (hA : A ⊆ Set.Ioi 0)
    (hdA : HasDensity A a)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε)
    (m : ℕ+) (R : Finset (ZMod (m : ℕ)))
    (hR : internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) m)) ⁻¹' (R : Set _)) :
    ∃ S : Finset (ZMod (m : ℕ)), DensityEquivalent A (periodicSet S) := by
  let S := R.image (fun r => r + finiteValue U (fun n => (start n : ZMod (m : ℕ))))
  have hprofile := actual_window_profile_of_residue_mask U hU q m (hdiv m) A start R hR
  exact ⟨S, loeb_regular_window_global_mask U hU q hdiv A start a hA hdA hmA happrox m S
    (actual_window_mask_of_indicator_profile U hU q m (hdiv m) A start S hprofile)⟩

end Erdos335.Loeb

end
