import Erdos335.LoebActualFiberTranslations
import Erdos335.LoebActiveFiberPeriods

/-!
# Translating full physical residue fibers
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance fullFiberTranslationsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_vadd_subset_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hST : S ≤ᵐ[loebMeasure U hU] T) :
    t +ᵥ S ≤ᵐ[loebMeasure U hU] t +ᵥ T := by
  have hinter : S ∩ T =ᵐ[loebMeasure U hU] S := by
    filter_upwards [hST] with x hx
    exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
  have htranslate := loeb_vadd_congr_ae U hU _ _ t hinter
  have hsub : t +ᵥ (S ∩ T) ⊆ t +ᵥ T := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, hy.2, rfl⟩
  exact htranslate.symm.le.trans hsub.eventuallySubset

theorem window_residue_fiber_nat_translate
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (start : ℕ → ℕ)
    (r : ZMod (h : ℕ)) (u : ℕ) :
    productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
      (windowResidueMap U q h start ⁻¹' {r}) =
        windowResidueMap U q h start ⁻¹' {r + (u : ZMod (h : ℕ))} := by
  let t := productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ)))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change windowResidueMap U q h start (t + y) = r + (u : ZMod (h : ℕ))
    rw [windowResidueMap_nat_translate U q h hd start u y,
      show windowResidueMap U q h start y = r from hy]
  · intro hx
    have hid : t + (x - t) = x := by abel
    refine ⟨x - t, ?_, hid⟩
    have hmap := windowResidueMap_nat_translate U q h hd start u (x - t)
    change windowResidueMap U q h start (t + (x - t)) =
      windowResidueMap U q h start (x - t) + (u : ZMod (h : ℕ)) at hmap
    rw [hid, show windowResidueMap U q h start x = r + (u : ZMod (h : ℕ)) from hx] at hmap
    exact add_right_cancel hmap.symm

theorem actual_full_fiber_translate_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (r : ZMod (h : ℕ))
    (hfull : actualWindowProfile U hU q h A start r = 1) (u : ℕ) :
    windowResidueMap U q h start ⁻¹' {r + (u : ZMod (h : ℕ))} ≤ᵐ[loebMeasure U hU]
      productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
        internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  have hsub := actual_window_full_mask_subset U hU q h hd A start {r} (by
    intro s hs
    have hsr : s = r := Finset.mem_singleton.mp hs
    simpa only [hsr] using hfull)
  have htranslate := loeb_vadd_subset_ae U hU q _ _
    (productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ)))) hsub
  simpa only [Finset.coe_singleton, window_residue_fiber_nat_translate U q h hd start r u] using htranslate

end Erdos335.Loeb

end
