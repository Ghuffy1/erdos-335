import Erdos335.LoebStrictPeriodicWindowCore

/-!
# Periodic baseline reduction at a prescribed finite quotient
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance fixedPeriodicCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_fixed_periodic_core_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m h : ℕ+) (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ)) (hhm : (h : ℕ) ∣ (m : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (P : Finset (ZMod (m : ℕ)))
    (hP : ∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0)
    (hpre : (naturalCyclicProjection m h) ⁻¹'
      (((P + residues (m : ℕ) B).image (naturalCyclicProjection m h) : Finset (ZMod (h : ℕ))) :
        Set (ZMod (h : ℕ))) = ((P + residues (m : ℕ) B : Finset (ZMod (m : ℕ))) : Set (ZMod (m : ℕ)))) :
    let S := P.image (naturalCyclicProjection m h)
    S ⊆ residues (h : ℕ) A ∧
      (∀ r ∉ S, actualWindowProfile U hU q h A start r = 0) ∧
      ∀ r ∈ S + residues (h : ℕ) B, actualWindowProfile U hU q h (A + B) start r = 1 := by
  classical
  dsimp only
  let π := naturalCyclicProjection m h
  let S := P.image π
  have hd' : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := hd.mono fun n hn => dvd_trans hhm hn
  have hBimage : (residues (m : ℕ) B).image π = residues (h : ℕ) B :=
    residues_image_of_natCast m h π (fun n => naturalCyclicProjection_natCast m h hhm n) B
  have himage : (P + residues (m : ℕ) B).image π = S + residues (h : ℕ) B := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_add, Set.image_add, ← Finset.coe_image,
      ← Finset.coe_image, hBimage, Finset.coe_add]
  have hSsub : S ⊆ residues (h : ℕ) A := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    have hvA : v ∈ residues (m : ℕ) A := by
      by_contra hn
      have hz := actual_window_profile_zero_outside_residues U hU q m hd A start v hn
      change actualWindowProfile U hU q m A start v = 0 at hz
      have ho := hP v
      rw [if_pos hv] at ho
      linarith
    obtain ⟨n, hn, hnv⟩ := mem_residues.mp hvA
    exact mem_residues.mpr ⟨n, hn, by rw [← hnv, naturalCyclicProjection_natCast m h hhm]⟩
  have hmask := actual_window_mask_of_indicator_profile U hU q m hd A start P hP
  have hAsub : internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      ≤ᵐ[loebMeasure U hU] windowResidueMap U q h start ⁻¹' (S : Set _) := by
    filter_upwards [hmask] with x hx hxA
    have hxP : windowResidueMap U q m start x ∈ P := Eq.mp hx hxA
    exact Finset.mem_image.mpr ⟨_, hxP, windowResidueMap_refinement U q m h start hd hhm x⟩
  have hpull : windowResidueMap U q h start ⁻¹'
      ((S + residues (h : ℕ) B : Finset (ZMod (h : ℕ))) : Set (ZMod (h : ℕ))) =
      windowResidueMap U q m start ⁻¹'
        ((P + residues (m : ℕ) B : Finset (ZMod (m : ℕ))) : Set (ZMod (m : ℕ))) := by
    ext x
    change windowResidueMap U q h start x ∈ S + residues (h : ℕ) B ↔
      windowResidueMap U q m start x ∈ P + residues (m : ℕ) B
    rw [← himage, ← windowResidueMap_refinement U q m h start hd hhm x]
    exact Iff.of_eq (congrArg (fun V : Set (ZMod (m : ℕ)) => windowResidueMap U q m start x ∈ V) hpre)
  have hfull : ∀ r ∈ P + residues (m : ℕ) B,
      actualWindowProfile U hU q m (A + B) start r = 1 := by
    simpa only [add_comm B A, add_comm (residues (m : ℕ) B) P] using
      actual_periodic_input_baseline U hU q hq m hd B A start P hP
  have hCsub := actual_window_full_mask_subset U hU q m hd (A + B) start _ hfull
  rw [← hpull] at hCsub
  exact ⟨hSsub, actual_window_zero_off_mask U hU q h A start S hAsub,
    actual_window_full_on_mask U hU q h hd' (A + B) start _ hCsub⟩

end Erdos335.Loeb

end
