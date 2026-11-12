import Erdos335.LoebNullFrameMass

/-!
# Lifting an active-fiber period through full background residues
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance activeFiberPeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem window_mask_period_of_kernel
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+) (start : ℕ → ℕ)
    (R : Finset (ZMod (h : ℕ)))
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (ht : finiteQuotient U (fun n => naturalCyclicProjection (q n) h) t = 0) :
    t +ᵥ (windowResidueMap U q h start ⁻¹' (R : Set _)) =
      windowResidueMap U q h start ⁻¹' (R : Set _) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change finiteQuotient U (fun n => naturalCyclicProjection (q n) h) (t + y) + _ ∈ R
    rw [map_add, ht, zero_add]
    exact hy
  · intro hx
    refine ⟨-t + x, ?_, by simp only [vadd_eq_add, add_neg_cancel_left]⟩
    change finiteQuotient U (fun n => naturalCyclicProjection (q n) h) (-t + x) + _ ∈ R
    rw [map_add, map_neg, ht, neg_zero, zero_add]
    exact hx

theorem actual_window_active_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (i : ZMod (h : ℕ))
    (hfull : ∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1) :
    internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU] actualWindowFiber U q h A start i ∪
        windowResidueMap U q h start ⁻¹' ((residues (h : ℕ) A).erase i : Set _) := by
  have hb := actual_window_full_mask_subset U hU q h hd A start ((residues (h : ℕ) A).erase i) hfull
  filter_upwards [hb] with x hx
  apply propext
  constructor
  · intro hA
    by_cases hi : windowResidueMap U q h start x = i
    · exact Or.inl ⟨hA, hi⟩
    · exact Or.inr (Finset.mem_erase.mpr ⟨hi, actual_residue_of_internal_cyclic_window U q h hd A start x hA⟩)
  · rintro (hactive | hbackground)
    · exact hactive.1
    · exact hx hbackground

theorem actual_window_period_of_active_fiber
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (i : ZMod (h : ℕ))
    (hfull : ∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1)
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (ht : finiteQuotient U (fun n => naturalCyclicProjection (q n) h) t = 0)
    (hactive : t +ᵥ actualWindowFiber U q h A start i =ᵐ[loebMeasure U hU]
      actualWindowFiber U q h A start i) :
    t +ᵥ internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU]
        internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  have hsplit := actual_window_active_background U hU q h hd A start i hfull
  have htranslate := loeb_vadd_congr_ae U hU _ _ t hsplit
  rw [vadd_set_union, window_mask_period_of_kernel U q h start _ t ht] at htranslate
  have hmiddle : (t +ᵥ actualWindowFiber U q h A start i) ∪
      windowResidueMap U q h start ⁻¹' ((residues (h : ℕ) A).erase i : Set _) =ᵐ[loebMeasure U hU]
        actualWindowFiber U q h A start i ∪
          windowResidueMap U q h start ⁻¹' ((residues (h : ℕ) A).erase i : Set _) := by
    filter_upwards [hactive] with x hx
    simp only [Set.mem_union, hx]
  exact htranslate.trans (hmiddle.trans hsplit.symm)

end Erdos335.Loeb

end
