import Erdos335.LoebFullFiberTranslations
import Erdos335.LoebNullFrameMass
import Erdos335.LoebFixedShiftWindow
import Erdos335.MaskCoverage

/-!
# Finite literal representatives cover an actual null-frame window
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance actualNullCoverageLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_null_frame_finite_coverage
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (i j : ZMod (h : ℕ))
    (hi : i ∈ residues (h : ℕ) A) (hj : j ∈ residues (h : ℕ) B)
    (ha : a = (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ))
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hcard : (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
      (residues (h : ℕ) A).card + (residues (h : ℕ) B).card)
    (hAfull : ∀ r ∈ (residues (h : ℕ) A).erase i, actualWindowProfile U hU q h A start r = 1)
    (hBfull : ∀ r ∈ (residues (h : ℕ) B).erase j, actualWindowProfile U hU q h B start r = 1)
    (FA FB : Finset ℕ) (hFA : (FA : Set ℕ) ⊆ A) (hFB : (FB : Set ℕ) ⊆ B)
    (hrepA : ∀ r ∈ residues (h : ℕ) A, ∃ u ∈ FA, (u : ZMod (h : ℕ)) = r)
    (hrepB : ∀ r ∈ residues (h : ℕ) B, ∃ v ∈ FB, (v : ZMod (h : ℕ)) = r) :
    internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU]
        internalSet U (fun n => (cyclicWindow (Proposed.finiteTranslateCover A B FA FB)
          (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  classical
  let K := Proposed.finiteTranslateCover A B FA FB
  let WK := internalSet U (fun n => (cyclicWindow K (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  have win_mono (X Y : Set ℕ) (hXY : X ⊆ Y) :
      internalSet U (fun n => (cyclicWindow X (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) ⊆
        internalSet U (fun n => (cyclicWindow Y (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
    apply (internalSet_subset_iff U _ _).mpr
    apply Eventually.of_forall
    intro n x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hXY (Finset.mem_filter.mp hx).2⟩
  have leftShift (v : ℕ) (hv : v ∈ FB) : shift A v ⊆ K := by
    intro n hn
    exact Or.inl ⟨v, hv, hn⟩
  have rightShift (u : ℕ) (hu : u ∈ FA) : shift B u ⊆ K := by
    intro n hn
    exact Or.inr ⟨u, hu, hn⟩
  have shifted (X : Set ℕ) (u : ℕ) (hX : shift X u ⊆ K) :
      productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
        internalSet U (fun n => (cyclicWindow X (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
          ≤ᵐ[loebMeasure U hU] WK :=
    (loeb_fixed_shift_window_eq U hU q hq X start u).le.trans (win_mono (shift X u) K hX).eventuallySubset
  have hmass := null_frame_active_measures_equal U hU q hq h hd A B start a b i j hi hj ha hmB hmC
    hcard hAfull hBfull
  have fiber (w : ZMod (h : ℕ)) (hw : w ∈ residues (h : ℕ) (A + B)) :
      actualWindowFiber U q h (A + B) start w ≤ᵐ[loebMeasure U hU] WK := by
    by_cases hactive : w = i + j
    · obtain ⟨u, hu, hui⟩ := hrepA i hi
      have heq := actual_window_fiber_equal_translate U hU q hq h hd A B start u (hFA hu) j
        (by simpa only [hui] using hmass)
      rw [hui] at heq
      have hsub : productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
          actualWindowFiber U q h B start j ⊆
            productProjection (U : Filter ℕ) (fun n => (u : ZMod (q n : ℕ))) +ᵥ
              internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
        rintro x ⟨y, hy, rfl⟩
        exact ⟨y, hy.1, rfl⟩
      rw [hactive]
      exact heq.symm.le.trans (hsub.eventuallySubset.trans (shifted B u (rightShift u hu)))
    · rw [residues_add] at hw
      obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hw
      by_cases hri : r = i
      · have htj : t ≠ j := by
          intro htj
          exact hactive (by rw [hri, htj])
        obtain ⟨u, hu, hur⟩ := hrepA r hr
        have hfill := actual_full_fiber_translate_subset U hU q h hd B start t
          (hBfull t (Finset.mem_erase.mpr ⟨htj, ht⟩)) u
        have hcover := hfill.trans (shifted B u (rightShift u hu))
        have htarget : windowResidueMap U q h start ⁻¹' {r + t} ≤ᵐ[loebMeasure U hU] WK := by
          simpa only [hur, add_comm t r] using hcover
        exact inter_subset_right.eventuallySubset.trans htarget
      · obtain ⟨v, hv, hvt⟩ := hrepB t ht
        have hfill := actual_full_fiber_translate_subset U hU q h hd A start r
          (hAfull r (Finset.mem_erase.mpr ⟨hri, hr⟩)) v
        have hcover := hfill.trans (shifted A v (leftShift v hv))
        have htarget : windowResidueMap U q h start ⁻¹' {r + t} ≤ᵐ[loebMeasure U hU] WK := by
          simpa only [hvt] using hcover
        exact inter_subset_right.eventuallySubset.trans htarget
  have hall : ∀ w : ZMod (h : ℕ), ∀ᵐ x ∂loebMeasure U hU,
      w ∈ residues (h : ℕ) (A + B) → x ∈ actualWindowFiber U q h (A + B) start w → x ∈ WK := by
    intro w
    by_cases hw : w ∈ residues (h : ℕ) (A + B)
    · filter_upwards [fiber w hw] with x hx _ hmem
      exact hx hmem
    · exact Eventually.of_forall fun x hx => False.elim (hw hx)
  have hforward : internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) :
      Set (ZMod (q n : ℕ)))) ≤ᵐ[loebMeasure U hU] WK := by
    filter_upwards [ae_all_iff.mpr hall] with x hx hC
    exact hx (windowResidueMap U q h start x)
      (actual_residue_of_internal_cyclic_window U q h hd (A + B) start x hC) ⟨hC, rfl⟩
  have hK : K ⊆ A + B := by
    rintro n (⟨v, hv, x, hx, rfl⟩ | ⟨u, hu, y, hy, rfl⟩)
    · exact ⟨x, hx, v, hFB hv, rfl⟩
    · exact ⟨u, hFA hu, y, hy, Nat.add_comm _ _⟩
  exact hforward.antisymm (win_mono K (A + B) hK).eventuallySubset

end Erdos335.Loeb

end
