import Erdos335.ConstrainedPhysicalProfileLimits

/-!
# Ordinary residue densities identify every actual prefix model

Private proof development. Verification status is recorded separately. Literal residue intersections include zero
when the original set includes zero. No positivity convention is needed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance ordinaryPrefixProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_zero_prefix_profile_of_density
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (hq : Tendsto (fun s => (q s : ℕ)) atTop atTop)
    (m : ℕ+) (hd : ∀ᶠ s in U, (m : ℕ) ∣ (q s : ℕ))
    (A : Set ℕ) (r : ZMod (m : ℕ)) (v : ℝ)
    (hdensity : HasDensity {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
      (v / (m : ℕ))) :
    actualWindowProfile U hU q m A (fun _ => 0) r = v := by
  have hcounts := ((hasDensity_iff_prefixCount _ _).mp hdensity).comp hq
  have hscaled := hcounts.const_mul ((m : ℕ) : ℝ)
  have hmne : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hvalue : ((m : ℕ) : ℝ) * (v / (m : ℕ)) = v := by field_simp [hmne]
  rw [hvalue] at hscaled
  have hzero (S : Set ℕ) : tailShift S 0 = S := by
    ext n
    simp [tailShift]
  have hcyclic : Tendsto (fun s => ((m : ℕ) : ℝ) *
      (((cyclicWindow {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
        0 (q s : ℕ)).card : ℝ) / (q s : ℕ))) atTop (𝓝 v) := by
    simpa only [Function.comp_def, cyclicWindow_card_eq_prefixCount, hzero] using hscaled
  have hactual := actual_window_profile_tendsto_absolute_counts U hU q m hd A (fun _ => 0) r
  exact tendsto_nhds_unique hactual (hcyclic.mono_left hU)

end Erdos335.Loeb

end
