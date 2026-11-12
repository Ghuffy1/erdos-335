import Erdos335.LoebSaturatedNullFrame
import Erdos335.LoebUniformActualNullPeriods
import Erdos335.LoebActualNullCoverage
import Erdos335.LoebShiftedProfileMasks
import Erdos335.StabilizerPullback

/-!
# Common integer periods and coverage from actual null frames

Private proof development. Verification status is recorded separately.
The finite period family is chosen before the ultrafilter and local model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance commonNullPeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem ActualWindowNullFrame.integer_multiple_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a : ℝ)
    (hframe : ActualWindowNullFrame U hU q h A B start a)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (t : ℕ) (ht : (h : ℕ) ∣ t) :
    productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ))) +ᵥ
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU]
          internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  classical
  obtain ⟨i, j, hi, _, ha, _, hAfull, _⟩ := hframe
  let W := internalSet U
    (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  let R := (residues (h : ℕ) A).erase i
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  let p := productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ)))
  have hzero : actualWindowProfile U hU q h A start i = 0 := by
    rw [actual_window_exceptional_profile U hU q h hd A start i hi hAfull, hmA, ha]
    have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
    field_simp [hh] <;> ring
  have hprofile : ∀ r, actualWindowProfile U hU q h A start r = if r ∈ R then (1 : ℝ) else 0 := by
    intro r
    by_cases hr : r ∈ R
    · rw [if_pos hr]
      exact hAfull r hr
    · rw [if_neg hr]
      by_cases hri : r = i
      · simpa only [hri] using hzero
      · apply actual_window_profile_zero_outside_residues U hU q h hd A start r
        intro hrA
        exact hr (Finset.mem_erase.mpr ⟨hri, hrA⟩)
  have hmask : W =ᵐ[loebMeasure U hU] φ ⁻¹' (R.image (fun r => r - z) : Set _) :=
    loeb_ae_eq_shifted_mask_of_full_profile U hU q h hd W (measurable_internalSet U _) R z hprofile
  have hφp : φ p = 0 := by
    have hnat := finiteQuotient_natCast_of_eventually U q h
      (fun n => naturalCyclicProjection (q n) h)
      (hd.mono fun n hn k => naturalCyclicProjection_natCast (q n) h hn k) t
    change φ p = (t : ZMod (h : ℕ)) at hnat
    rw [hnat]
    exact (ZMod.natCast_eq_zero_iff t (h : ℕ)).mpr ht
  have hperiod : p +ᵥ (φ ⁻¹' (R.image (fun r => r - z) : Set _)) =
      φ ⁻¹' (R.image (fun r => r - z) : Set _) := by
    rw [← preimage_vadd_addHom, hφp, zero_vadd]
  have hmove := loeb_vadd_congr_ae U hU W _ p hmask
  rw [hperiod] at hmove
  exact hmove.trans hmask.symm

theorem exists_uniform_common_null_periods
    (A : Set ℕ) (a δ : ℝ) (hδ : 0 < δ)
    (hcapacity : ∀ k : ℕ+, a + δ ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ)) :
    ∃ D : Finset ℕ, (∀ t ∈ D, 0 < t) ∧
      ∀ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+),
        Tendsto (fun n => (q n : ℕ)) atTop atTop →
        ∀ (h : ℕ+), (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) →
        ∀ (B : Set ℕ) (start : ℕ → ℕ) (b : ℝ),
          ActualWindowNullFrame U hU q h A B start a →
          (loebMeasure U hU (internalSet U
            (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a →
          (loebMeasure U hU (internalSet U
            (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b →
          (loebMeasure U hU (internalSet U
            (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b →
          ∃ t ∈ D,
            (productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ))) +ᵥ
              internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
                =ᵐ[loebMeasure U hU]
                  internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) ∧
            (productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ))) +ᵥ
              internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
                =ᵐ[loebMeasure U hU]
                  internalSet U (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) ∧
            (productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ))) +ᵥ
              internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
                =ᵐ[loebMeasure U hU]
                  internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) := by
  let N := Nat.ceil (1 / δ)
  obtain ⟨D, hD, hselect⟩ := finite_residue_difference_representatives A N
  refine ⟨D, hD, ?_⟩
  intro U hU q hq h hd B start b hframe hmA hmB hmC
  obtain ⟨i, j, hi, hj, ha, hcard, hAfull, hBfull⟩ := hframe
  have hframe' : ActualWindowNullFrame U hU q h A B start a :=
    ⟨i, j, hi, hj, ha, hcard, hAfull, hBfull⟩
  have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hδh : δ ≤ 1 / (h : ℕ) := by
    have hc := hcapacity h
    rw [ha] at hc
    have heq : (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ) + 1 / (h : ℕ) =
        ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by ring
    linarith
  have hindex : ((h : ℕ) : ℝ) ≤ 1 / δ := by
    apply (le_div_iff₀ hδ).mpr
    have hp := (le_div_iff₀ hh).mp hδh
    simpa only [mul_comm] using hp
  have hleN : (h : ℕ) ≤ N := by exact_mod_cast hindex.trans (Nat.le_ceil (1 / δ))
  obtain ⟨u, hu, v, hv, huv, hui, hvi, hdiff⟩ := hselect h i hleN
    (positive_gap_null_class_has_two_points A a δ hδ hcapacity h i hi ha)
  have ht : (h : ℕ) ∣ v - u := by
    apply (ZMod.natCast_eq_zero_iff (v - u) (h : ℕ)).mp
    rw [Nat.cast_sub huv.le, hvi, hui, sub_self]
  have hAperiod := ActualWindowNullFrame.integer_multiple_period U hU q h hd A B start a
    hframe' hmA (v - u) ht
  have hBC := null_frame_integer_difference_periods U hU q hq h hd A B start a b i j
    hi hj ha hmB hmC hcard hAfull hBfull u v hu hv huv hui hvi
  exact ⟨v - u, hdiff, hAperiod, hBC.1, hBC.2⟩

theorem ActualWindowNullFrame.finite_coverage
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ)
    (hframe : ActualWindowNullFrame U hU q h A B start a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (FA FB : Finset ℕ) (hFA : (FA : Set ℕ) ⊆ A) (hFB : (FB : Set ℕ) ⊆ B)
    (hrepA : ∀ r ∈ residues (h : ℕ) A, ∃ u ∈ FA, (u : ZMod (h : ℕ)) = r)
    (hrepB : ∀ r ∈ residues (h : ℕ) B, ∃ v ∈ FB, (v : ZMod (h : ℕ)) = r) :
    internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU]
        internalSet U (fun n => (cyclicWindow (Proposed.finiteTranslateCover A B FA FB)
          (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  obtain ⟨i, j, hi, hj, ha, hcard, hAfull, hBfull⟩ := hframe
  exact actual_null_frame_finite_coverage U hU q hq h hd A B start a b i j hi hj ha hmB hmC
    hcard hAfull hBfull FA FB hFA hFB hrepA hrepB

end Erdos335.Loeb

end
