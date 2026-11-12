import Erdos335.NaturalQuotientRefinement
import Erdos335.LoebFullMaskProfiles
import Erdos335.LoebPeriodicWindowProfiles

/-!
# Physical residue maps and full-mask transfer for actual windows
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance windowResidueRefinementLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

def windowResidueMap (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+) (start : ℕ → ℕ)
    (x : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) : ZMod (h : ℕ) :=
  finiteQuotient U (fun n => naturalCyclicProjection (q n) h) x +
    finiteValue U (fun n => (start n : ZMod (h : ℕ)))

theorem windowResidueMap_fiber (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+)
    (start : ℕ → ℕ) (r : ZMod (h : ℕ)) :
    windowResidueMap U q h start ⁻¹' {r} =
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹'
        {r - finiteValue U (fun n => (start n : ZMod (h : ℕ)))} := by
  ext x
  change (_ + _ = r) ↔ (_ = r - _)
  exact eq_sub_iff_add_eq.symm

theorem windowResidueMap_preimage (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+)
    (start : ℕ → ℕ) (R : Finset (ZMod (h : ℕ))) :
    windowResidueMap U q h start ⁻¹' (R : Set _) =
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹'
        (R.image (fun r => r - finiteValue U (fun n => (start n : ZMod (h : ℕ)))) : Set _) := by
  classical
  ext x
  change _ + _ ∈ R ↔ _ ∈ R.image _
  constructor
  · intro hx
    exact Finset.mem_image.mpr ⟨_, hx, add_sub_cancel_right _ _⟩
  · intro hx
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hx
    rw [← heq, sub_add_cancel]
    exact hr

theorem windowResidueMap_refinement
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h k : ℕ+) (start : ℕ → ℕ)
    (hhq : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hkh : (k : ℕ) ∣ (h : ℕ))
    (x : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    naturalCyclicProjection h k (windowResidueMap U q h start x) = windowResidueMap U q k start x := by
  have hphase : naturalCyclicProjection h k (finiteValue U (fun n => (start n : ZMod (h : ℕ)))) =
      finiteValue U (fun n => (start n : ZMod (k : ℕ))) := by
    apply (finiteValue_eq_of_eventually U _ _ ?_).symm
    exact (eventually_eq_finiteValue U (fun n => (start n : ZMod (h : ℕ)))).mono fun n hn => by
      rw [← hn, naturalCyclicProjection_natCast h k hkh]
  unfold windowResidueMap
  rw [map_add, hphase]
  exact congrArg (fun y => y + finiteValue U (fun n => (start n : ZMod (k : ℕ))))
    (congrArg (fun f => f x) (finiteQuotient_natural_refinement U q h k hhq hkh))

theorem actual_window_full_mask_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (R : Finset (ZMod (h : ℕ))) (hfull : ∀ r ∈ R, actualWindowProfile U hU q h A start r = 1) :
    windowResidueMap U q h start ⁻¹' (R : Set _) ≤ᵐ[loebMeasure U hU]
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  rw [windowResidueMap_preimage]
  apply loeb_mask_ae_subset_of_full_profiles U hU q h hd _ (measurable_internalSet U _)
  intro r hr
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
  exact hfull t ht

theorem actual_window_full_on_mask
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (R : Finset (ZMod (h : ℕ)))
    (hsub : windowResidueMap U q h start ⁻¹' (R : Set _) ≤ᵐ[loebMeasure U hU]
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    ∀ r ∈ R, actualWindowProfile U hU q h A start r = 1 := by
  intro r hr
  apply loebResidueProfile_one_of_fiber_ae_subset U hU q h hd
  have hfiber : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹'
      {r - finiteValue U (fun n => (start n : ZMod (h : ℕ)))} ⊆
        windowResidueMap U q h start ⁻¹' (R : Set _) := by
    rw [← windowResidueMap_fiber]
    intro x hx
    change windowResidueMap U q h start x ∈ R
    rw [show windowResidueMap U q h start x = r from hx]
    exact hr
  exact hfiber.eventuallySubset.trans hsub

theorem loebMeasure_windowResidueMap_preimage
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (start : ℕ → ℕ)
    (R : Finset (ZMod (h : ℕ))) :
    loebMeasure U hU (windowResidueMap U q h start ⁻¹' (R : Set _)) =
      (R.card : ℝ≥0∞) / (h : ℕ) := by
  classical
  rw [windowResidueMap_preimage, loebMeasure_naturalCyclicProjection_preimage U hU q h hd]
  congr 2
  apply Finset.card_image_of_injective
  intro a b hab
  have ht := congrArg (fun r => r + finiteValue U (fun n => (start n : ZMod (h : ℕ)))) hab
  simpa only [sub_add_cancel] using ht

theorem actual_window_zero_off_mask
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (A : Set ℕ) (start : ℕ → ℕ) (R : Finset (ZMod (h : ℕ)))
    (hsub : internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      ≤ᵐ[loebMeasure U hU] windowResidueMap U q h start ⁻¹' (R : Set _)) :
    ∀ r ∉ R, actualWindowProfile U hU q h A start r = 0 := by
  classical
  let W := internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  let D := W ∩ windowResidueMap U q h start ⁻¹' (R : Set _)
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  have hDAE : D =ᵐ[loebMeasure U hU] W := by
    filter_upwards [hsub] with x hx
    exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
  have hDsub : D ⊆ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹'
      (R.image (fun r => r - z) : Set _) := by
    rw [← windowResidueMap_preimage]
    exact inter_subset_right
  intro r hr
  unfold actualWindowProfile
  rw [← loebResidueProfile_eq_of_ae U hU q h D W hDAE]
  apply loebResidueProfile_zero_of_subset U hU q h D _ hDsub
  intro hm
  obtain ⟨t, ht, htr⟩ := Finset.mem_image.mp hm
  have hEq : t = r := by
    have he := congrArg (fun v => v + z) htr
    simpa only [z, sub_add_cancel] using he
  exact hr (hEq ▸ ht)

end Erdos335.Loeb

end
