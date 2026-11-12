import Erdos335.LoebWindowProfiles
import Erdos335.LoebPeriodicWindowProfiles

/-!
# Physical residue-count limits at a fixed reference window length

Private proof development. Verification status is recorded separately. The moving window keeps its absolute integer
residue label while the relative cyclic phase is fixed along the ultrafilter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance physicalProfileLimitsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_window_profile_tendsto_absolute_counts
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m : ℕ+) (hd : ∀ᶠ s in U, (m : ℕ) ∣ (q s : ℕ))
    (A : Set ℕ) (start : ℕ → ℕ) (r : ZMod (m : ℕ)) :
    Tendsto (fun s => ((m : ℕ) : ℝ) *
      (((cyclicWindow {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
        (start s) (q s : ℕ)).card : ℝ) / (q s : ℕ))) (U : Filter ℕ)
      (𝓝 (actualWindowProfile U hU q m A start r)) := by
  classical
  let z := finiteValue U (fun s => (start s : ZMod (m : ℕ)))
  have hphase : ∀ᶠ s in U, (start s : ZMod (m : ℕ)) = z :=
    eventually_eq_finiteValue U (fun s => (start s : ZMod (m : ℕ)))
  have hsets : ∀ᶠ s in U,
      cyclicWindow {n : ℕ | n ∈ A ∧ ((n - start s : ℕ) : ZMod (m : ℕ)) = r - z}
        (start s) (q s : ℕ) =
      cyclicWindow {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
        (start s) (q s : ℕ) := by
    filter_upwards [hphase] with s hs
    ext x
    simp only [cyclicWindow, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq, Nat.add_sub_cancel_left, Nat.cast_add, hs]
    constructor
    · rintro ⟨hAx, hx⟩
      exact ⟨hAx, by simpa only [eq_sub_iff_add_eq, add_comm] using hx⟩
    · rintro ⟨hAx, hx⟩
      exact ⟨hAx, by simpa only [eq_sub_iff_add_eq, add_comm] using hx⟩
  have hraw := (loeb_window_residue_measure_tendsto U hU q m hd
    (fun _ => A) start (r - z)).const_mul ((m : ℕ) : ℝ)
  have hlimit : Tendsto (fun s => ((m : ℕ) : ℝ) *
      (((cyclicWindow {n : ℕ | n ∈ A ∧ ((n - start s : ℕ) : ZMod (m : ℕ)) = r - z}
        (start s) (q s : ℕ)).card : ℝ) / (q s : ℕ))) (U : Filter ℕ)
      (𝓝 (actualWindowProfile U hU q m A start r)) := by
    simpa only [actualWindowProfile, loebResidueProfile, mul_div_assoc] using hraw
  apply hlimit.congr'
  filter_upwards [hsets] with s hs
  rw [hs]

theorem reference_window_profile_tendsto_of_actual_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : ℕ → ℕ) (q : ℕ → ℕ+) (hH : ∀ s, 0 < H s)
    (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hgap : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0))
    (A : Set ℕ) (start : ℕ → ℕ) (m : ℕ+)
    (hd : ∀ᶠ s in U, (m : ℕ) ∣ (q s : ℕ)) (r : ZMod (m : ℕ))
    (v : ℝ) (hprofile : actualWindowProfile U hU q m A start r = v) :
    Tendsto (fun s => ((m : ℕ) : ℝ) *
      (((@cyclicWindow {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
        (start s) (H s) ⟨(hH s).ne'⟩).card : ℝ) / H s)) (U : Filter ℕ) (𝓝 v) := by
  letI (s : ℕ) : NeZero (H s) := ⟨(hH s).ne'⟩
  let qH : ℕ → ℕ+ := fun s => ⟨H s, hH s⟩
  have hHgap : Tendsto (fun s => (((qH s : ℕ) - H s : ℕ) : ℝ) / (qH s : ℕ))
      atTop (𝓝 0) := by
    change Tendsto (fun s => (((H s - H s : ℕ) : ℝ) / H s)) atTop (𝓝 0)
    simpa only [Nat.sub_self, Nat.cast_zero, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hnear := selected_cyclic_profiles_agree
    (fun _ => {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}) start H q qH
    hH hHq (fun _ => le_rfl) hgap hHgap
  have hnearScaled := (hnear.const_mul ((m : ℕ) : ℝ)).mono_left hU
  have hqLimit := actual_window_profile_tendsto_absolute_counts U hU q m hd A start r
  rw [hprofile] at hqLimit
  have hresult := hqLimit.sub hnearScaled
  simp only [mul_zero, sub_zero] at hresult
  apply hresult.congr
  intro s
  simp only [qH, PNat.mk_coe]
  ring

end Erdos335.Loeb

end
