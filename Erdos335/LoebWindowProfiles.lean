import Erdos335.NaturalCyclicProjection
import Erdos335.SelectedLengthComparison
import Erdos335.LoebCyclicModelMeasures

/-!
# Finite residue profiles agree across the two cyclic window models
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance windowProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_finset_quotient_fiber_tendsto
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (A : ∀ n, Finset (ZMod (q n : ℕ)))
    (p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ)) (r : ZMod (h : ℕ)) :
    Tendsto (fun n => (((A n).filter (fun x => p n x = r)).card : ℝ) / (q n : ℕ)) (U : Filter ℕ)
      (𝓝 (loebMeasure U hU
        (internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))) ∩ (finiteQuotient U p) ⁻¹' {r})).toReal) := by
  classical
  have heq : internalSet U (fun n => (((A n).filter (fun x => p n x = r)) : Set (ZMod (q n : ℕ)))) =
      internalSet U (fun n => (A n : Set (ZMod (q n : ℕ)))) ∩ (finiteQuotient U p) ⁻¹' {r} := by
    rw [finiteQuotient_preimage_internal, ← internalSet_inter]
    congr 1
    funext n
    ext x
    simp
  rw [← heq]
  exact loeb_finset_measure_tendsto U hU q (fun n => (A n).filter (fun x => p n x = r))

theorem naturalCyclicProjection_window_filter (q h : ℕ+) (hd : (h : ℕ) ∣ (q : ℕ))
    (A : Set ℕ) (start : ℕ) (r : ZMod (h : ℕ)) :
    (cyclicWindow A start (q : ℕ)).filter (fun x => naturalCyclicProjection q h x = r) =
      cyclicWindow {n | n ∈ A ∧ ((n - start : ℕ) : ZMod (h : ℕ)) = r} start (q : ℕ) := by
  classical
  ext x
  simp [cyclicWindow, naturalCyclicProjection_val q h hd, Nat.add_sub_cancel_left]

theorem loeb_window_residue_measure_tendsto
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : ℕ → Set ℕ) (start : ℕ → ℕ) (r : ZMod (h : ℕ)) :
    Tendsto (fun s => ((cyclicWindow
      {n | n ∈ A s ∧ ((n - start s : ℕ) : ZMod (h : ℕ)) = r} (start s) (q s : ℕ)).card : ℝ) /
        (q s : ℕ)) (U : Filter ℕ)
      (𝓝 (loebMeasure U hU (internalSet U (fun s => (cyclicWindow (A s) (start s) (q s : ℕ) :
        Set (ZMod (q s : ℕ)))) ∩
          (finiteQuotient U (fun s => naturalCyclicProjection (q s) h)) ⁻¹' {r})).toReal) := by
  have ht := loeb_finset_quotient_fiber_tendsto U hU q h
    (fun s => cyclicWindow (A s) (start s) (q s : ℕ)) (fun s => naturalCyclicProjection (q s) h) r
  apply ht.congr'
  filter_upwards [hd] with s hs
  rw [naturalCyclicProjection_window_filter (q s) h hs]

theorem loeb_window_residue_measure_agreement
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ℕ → Set ℕ) (start H : ℕ → ℕ) (p q : ℕ → ℕ+)
    (hH : ∀ s, 0 < H s) (hHp : ∀ s, H s ≤ (p s : ℕ)) (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hp : Tendsto (fun s => (((p s : ℕ) - H s : ℕ) : ℝ) / (p s : ℕ)) atTop (𝓝 0))
    (hq : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0))
    (h : ℕ+) (hdp : ∀ᶠ s in atTop, (h : ℕ) ∣ (p s : ℕ))
    (hdq : ∀ᶠ s in atTop, (h : ℕ) ∣ (q s : ℕ)) (r : ZMod (h : ℕ)) :
    (loebMeasure U hU (internalSet U (fun s => (cyclicWindow (A s) (start s) (p s : ℕ) :
        Set (ZMod (p s : ℕ)))) ∩
      (finiteQuotient U (fun s => naturalCyclicProjection (p s) h)) ⁻¹' {r})).toReal =
    (loebMeasure U hU (internalSet U (fun s => (cyclicWindow (A s) (start s) (q s : ℕ) :
        Set (ZMod (q s : ℕ)))) ∩
      (finiteQuotient U (fun s => naturalCyclicProjection (q s) h)) ⁻¹' {r})).toReal := by
  have hleft := loeb_window_residue_measure_tendsto U hU p h (hdp.filter_mono hU) A start r
  have hright := loeb_window_residue_measure_tendsto U hU q h (hdq.filter_mono hU) A start r
  have hnear := selected_cyclic_profiles_agree
    (fun s => {n | n ∈ A s ∧ ((n - start s : ℕ) : ZMod (h : ℕ)) = r}) start H p q hH hHp hHq hp hq
  exact sub_eq_zero.mp (tendsto_nhds_unique (hleft.sub hright) (hnear.mono_left hU))

end Erdos335.Loeb

end
