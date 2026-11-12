import Erdos335.LoebResidueMaskProfiles
import Erdos335.LoebFiniteResidueProfiles

/-!
# Periodic masks from shifted full residue profiles
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance shiftedProfileMasksLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_ae_eq_shifted_mask_of_full_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hS : MeasurableSet S)
    (R : Finset (ZMod (h : ℕ))) (z : ZMod (h : ℕ))
    (hfull : ∀ r, loebResidueProfile U hU q h S (r - z) = if r ∈ R then (1 : ℝ) else 0) :
    S =ᵐ[loebMeasure U hU]
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R.image (fun r => r - z) : Set _) := by
  classical
  have hmem (r : ZMod (h : ℕ)) : r ∈ R.image (fun r => r - z) ↔ r + z ∈ R := by
    constructor
    · intro hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
      simpa only [sub_add_cancel] using ht
    · intro hr
      exact Finset.mem_image.mpr ⟨r + z, hr, add_sub_cancel_right _ _⟩
  apply loeb_ae_eq_residue_mask_of_profile U hU q h hd S hS (R.image (fun r => r - z))
  intro r
  have hr := hfull (r + z)
  rw [add_sub_cancel_right] at hr
  change ((h : ℕ) : ℝ) * (loebMeasure U hU
    (S ∩ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r})).toReal =
      if r + z ∈ R then (1 : ℝ) else 0 at hr
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  by_cases hR : r ∈ R.image (fun r => r - z)
  · rw [if_pos hR]
    rw [if_pos ((hmem r).mp hR)] at hr
    apply (eq_div_iff hh).mpr
    simpa only [mul_comm] using hr
  · rw [if_neg hR]
    have hn : r + z ∉ R := by simpa only [← hmem] using hR
    rw [if_neg hn] at hr
    exact (mul_eq_zero.mp hr).resolve_left hh

end Erdos335.Loeb

end
