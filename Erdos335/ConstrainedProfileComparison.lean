import Erdos335.LoebWindowProfiles
import Erdos335.LoebPeriodicWindowProfiles
import Erdos335.LoebProfileBounds

/-!
# Profile comparisons at constrained cyclic window lengths

Private proof development. Verification status is recorded separately.
The selected lengths lie above the same positive reference length `H`.
Moving-window comparisons use the same start and the physical residue phase.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance constrainedProfileComparisonLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

theorem constrained_length_gap_of_ratio
    (H : ℕ → ℕ) (q : ℕ → ℕ+) (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hratio : Tendsto (fun s => ((q s : ℕ) : ℝ) / H s) atTop (𝓝 1)) :
    Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ))
      atTop (𝓝 0) := by
  have hrecip : Tendsto (fun s => (H s : ℝ) / (q s : ℕ)) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hdifference : Tendsto (fun s => 1 - (H s : ℝ) / (q s : ℕ)) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hrecip
  apply hdifference.congr
  intro s
  rw [Nat.cast_sub (hHq s)]
  have hqne : ((q s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (q s).ne_zero
  field_simp
  <;> ring

theorem constrained_actual_window_profiles_agree
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (C : Set ℕ) (start H : ℕ → ℕ) (p q : ℕ → ℕ+)
    (hH : ∀ s, 0 < H s)
    (hHp : ∀ s, H s ≤ (p s : ℕ)) (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hp : Tendsto (fun s => (((p s : ℕ) - H s : ℕ) : ℝ) / (p s : ℕ)) atTop (𝓝 0))
    (hq : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0))
    (h : ℕ+) (hdp : ∀ᶠ s in atTop, (h : ℕ) ∣ (p s : ℕ))
    (hdq : ∀ᶠ s in atTop, (h : ℕ) ∣ (q s : ℕ)) (r : ZMod (h : ℕ)) :
    actualWindowProfile U hU p h C start r = actualWindowProfile U hU q h C start r := by
  unfold actualWindowProfile loebResidueProfile
  rw [loeb_window_residue_measure_agreement U hU (fun _ => C) start H p q
    hH hHp hHq hp hq h hdp hdq
    (r - finiteValue U (fun s => (start s : ZMod (h : ℕ))))]

theorem constrained_prefix_profile_eq_limit
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : ℕ → ℕ) (q : ℕ → ℕ+) (hH : ∀ s, 0 < H s)
    (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hgap : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0))
    (A : Set ℕ) (h : ℕ+) (hd : ∀ᶠ s in atTop, (h : ℕ) ∣ (q s : ℕ))
    (r : ZMod (h : ℕ)) (v : ℝ)
    (hlimit : Tendsto (fun s => ((h : ℕ) : ℝ) *
      ((prefixCount {n : ℕ | n ∈ A ∧ (n : ZMod (h : ℕ)) = r} (H s) : ℝ) / H s))
      atTop (𝓝 v)) :
    actualWindowProfile U hU q h A (fun _ => 0) r = v := by
  let qH : ℕ → ℕ+ := fun s => ⟨H s, hH s⟩
  have hzero (S : Set ℕ) : tailShift S 0 = S := by
    ext n
    simp [tailShift]
  have hHgap : Tendsto (fun s => (((qH s : ℕ) - H s : ℕ) : ℝ) / (qH s : ℕ))
      atTop (𝓝 0) := by
    change Tendsto (fun s => (((H s - H s : ℕ) : ℝ) / H s)) atTop (𝓝 0)
    simpa only [Nat.sub_self, Nat.cast_zero, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hnear := selected_cyclic_profiles_agree
    (fun _ => {n : ℕ | n ∈ A ∧ (n : ZMod (h : ℕ)) = r}) (fun _ => 0)
    H q qH hH hHq (fun _ => le_rfl) hgap hHgap
  have hnear' : Tendsto (fun s =>
      (prefixCount {n : ℕ | n ∈ A ∧ (n : ZMod (h : ℕ)) = r} (q s : ℕ) : ℝ) / (q s : ℕ) -
      (prefixCount {n : ℕ | n ∈ A ∧ (n : ZMod (h : ℕ)) = r} (H s) : ℝ) / H s)
      atTop (𝓝 0) := by
    simp only [cyclicWindow_card_eq_prefixCount, hzero] at hnear
    exact hnear
  have hnearScaled : Tendsto (fun s => ((h : ℕ) : ℝ) *
      ((prefixCount {n : ℕ | n ∈ A ∧ (n : ZMod (h : ℕ)) = r} (q s : ℕ) : ℝ) / (q s : ℕ) -
      (prefixCount {n : ℕ | n ∈ A ∧ (n : ZMod (h : ℕ)) = r} (H s) : ℝ) / H s))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hnear'.const_mul ((h : ℕ) : ℝ)
  have hqLimit : Tendsto (fun s => ((h : ℕ) : ℝ) *
      ((prefixCount {n : ℕ | n ∈ A ∧ (n : ZMod (h : ℕ)) = r} (q s : ℕ) : ℝ) / (q s : ℕ)))
      atTop (𝓝 v) := by
    have hsum := hnearScaled.add hlimit
    simp only [zero_add] at hsum
    apply hsum.congr
    intro s
    ring
  have hfiber := (loeb_window_residue_measure_tendsto U hU q h (hd.filter_mono hU)
    (fun _ => A) (fun _ => 0) r).const_mul ((h : ℕ) : ℝ)
  have hactual : Tendsto (fun s => ((h : ℕ) : ℝ) *
      ((prefixCount {n : ℕ | n ∈ A ∧ (n : ZMod (h : ℕ)) = r} (q s : ℕ) : ℝ) / (q s : ℕ)))
      (U : Filter ℕ) (𝓝 (actualWindowProfile U hU q h A (fun _ => 0) r)) := by
    simpa only [Nat.sub_zero, cyclicWindow_card_eq_prefixCount, hzero,
      actualWindowProfile, loebResidueProfile, Nat.cast_zero, finiteValue_const, sub_zero]
      using hfiber
  exact tendsto_nhds_unique hactual (hqLimit.mono_left hU)

theorem constrained_prefix_model_profile_eq_limit
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : ℕ → ℕ) (q : ℕ → ℕ+) (hH : ∀ s, 0 < H s)
    (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hgap : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0))
    (A : Set ℕ)
    (P : Set ((U : Filter ℕ).Product (fun s => ZMod (q s : ℕ))))
    (hP : P =ᵐ[loebMeasure U hU] internalSet U
      (fun s => (cyclicWindow A 0 (q s : ℕ) : Set (ZMod (q s : ℕ)))))
    (h : ℕ+) (hd : ∀ᶠ s in atTop, (h : ℕ) ∣ (q s : ℕ))
    (r : ZMod (h : ℕ)) (v : ℝ)
    (hlimit : Tendsto (fun s => ((h : ℕ) : ℝ) *
      ((prefixCount {n : ℕ | n ∈ A ∧ (n : ZMod (h : ℕ)) = r} (H s) : ℝ) / H s))
      atTop (𝓝 v)) :
    loebResidueProfile U hU q h P r = v := by
  have hprofile := loebResidueProfile_eq_of_ae U hU q h P
    (internalSet U (fun s => (cyclicWindow A 0 (q s : ℕ) : Set (ZMod (q s : ℕ)))))
      hP r
  have hactual := constrained_prefix_profile_eq_limit U hU H q hH hHq hgap A h hd r v hlimit
  have hzero : loebResidueProfile U hU q h
      (internalSet U (fun s => (cyclicWindow A 0 (q s : ℕ) : Set (ZMod (q s : ℕ))))) r =
      actualWindowProfile U hU q h A (fun _ => 0) r := by
    simp only [actualWindowProfile, Nat.cast_zero, finiteValue_const, sub_zero]
  exact hprofile.trans (hzero.trans hactual)

end Erdos335.Loeb

end
