import Erdos335.PeriodicRefinementPreparedScales
import Erdos335.PeriodicRefinementSampledConvolutionWindows
import Erdos335.PeriodicRefinementMacroWindowData

/-!
# Almost-everywhere prescribed windows on the whole positive axis
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale

noncomputable section

namespace Erdos335.PeriodicRefinement

def pairedModelIndex (L : ℕ+) (o : Bool) : ℕ :=
  2 * ((L : ℕ) - 1) + if o then 1 else 0

theorem paired_model_enlargement (L : ℕ+) (o : Bool) :
    modelEnlargement (pairedModelIndex L o) = L := by
  apply Subtype.ext
  change (2 * ((L : ℕ) - 1) + if o then 1 else 0) / 2 + 1 = (L : ℕ)
  have hL : (L : ℕ) - 1 + 1 = (L : ℕ) := Nat.sub_add_cancel L.pos
  cases o <;> simp <;> omega

theorem paired_model_moving (A B : Set ℕ) (L : ℕ+) (o : Bool) :
    modelMoving A B (pairedModelIndex L o) = if o then B else A := by
  cases o <;> simp [modelMoving, pairedModelIndex, Nat.add_mod, Nat.mul_mod]

theorem paired_model_other (A B : Set ℕ) (L : ℕ+) (o : Bool) :
    modelOther A B (pairedModelIndex L o) = if o then A else B := by
  cases o <;> simp [modelOther, pairedModelIndex, Nat.add_mod, Nat.mul_mod]

theorem PreparedMacroScales.exists_window_sequence
    {A B : Set ℕ} {a b : ℝ} {M : ℕ+} (p : PreparedMacroScales A B a b M) :
    ∃ (σ : ℕ → ℕ) (d : MacroWindowSequence A B a b M),
      StrictMono σ ∧ d.cutoff = p.cutoff ∘ σ ∧ d.cumulative = p.cumulative.curve := by
  classical
  obtain ⟨σ, hσ, hsample⟩ :=
    exists_ae_sampled_convolution_windows (modelMoving A B) (modelOther A B)
      p.cutoff p.lower p.upper p.width modelEnlargement p.cutoff_positive p.cutoff_tendsto
      p.width_positive p.width_tendsto p.lower_width p.width_upper p.width_cutoff
      (fun j => Classical.choice (p.model j))
  let N := p.cutoff ∘ σ
  let H := p.width ∘ σ
  let c : CompactCumulativeData A B M N := p.cumulative.subsequence σ hσ.tendsto_atTop
  have hN : ∀ n, 0 < N n := fun n => p.cutoff_positive (σ n)
  have hH : ∀ n, 0 < H n := fun n => p.width_positive (σ n)
  have hHtop : Tendsto H atTop atTop := p.width_tendsto.comp hσ.tendsto_atTop
  have hscale : Tendsto (fun n => (H n : ℝ) / N n) atTop (𝓝 0) :=
    p.width_cutoff.comp hσ.tendsto_atTop
  have hbudget (j : ℕ) : Tendsto
      (fun n => cumulativeErrorBudget c a b j n / H n) atTop (𝓝 0) := by
    exact (p.budget_small j).comp hσ.tendsto_atTop
  have hwindows : ∀ᵐ t : ℝ, 0 < t → Nonempty (ScheduledMacroWindow A B a b N H t) := by
    filter_upwards [hsample] with t ht htpos
    obtain ⟨k, hk⟩ := exists_nat_gt t
    have hkpos : 0 < k := by exact_mod_cast (htpos.trans hk)
    let L : ℕ+ := ⟨k, hkpos⟩
    let index := pairedModelIndex L
    have hex (o : Bool) := ht htpos (index o) (by
      have htL : t < (modelEnlargement (index o) : ℕ) := by
        dsimp only [index]
        rw [paired_model_enlargement]
        exact hk
      exact htL)
    choose q hq using hex
    have hindex : ((L : ℕ) - 1 : ℕ) + 1 = (L : ℕ) :=
      Nat.sub_add_cancel (by have := L.pos; omega)
    obtain ⟨hleft, hright, houtput⟩ := prefix_errors_small_of_budget_small c a b
      ((L : ℕ) - 1) H (hbudget ((L : ℕ) - 1))
    exact ⟨{
      enlargement := L
      parameter_lt := hk
      period := q
      length_lower := fun o => (hq o).1
      length_ratio := fun o => selected_length_ratio_of_gap H (q o) (hq o).1 (hq o).2.2.1
      divides := fun o k => (hq o).2.2.2.1 (k : ℕ) k.pos
      inside := by
        intro o
        simpa only [index, paired_model_enlargement, macroStart, N, H, Function.comp_def] using (hq o).2.2.2.2.1
      left_error := by simpa only [hindex] using hleft
      right_error := by simpa only [hindex] using hright
      output_error := by simpa only [hindex] using houtput
      convolution_error := by
        intro o
        simpa only [index, paired_model_moving, paired_model_other, macroStart, N, H, Function.comp_def] using (hq o).2.2.2.2.2
    }⟩
  let d : MacroWindowSequence A B a b M := {
    cutoff := N
    width := H
    cutoff_positive := hN
    width_positive := hH
    width_tendsto := hHtop
    width_ratio := hscale
    cumulative := c.curve
    cumulative_lipschitz := c.curve_lipschitz
    cumulative_zero := c.curve_zero
    approximation := cumulativeApproximationOfBudget c a b H hH hbudget
    windows := hwindows
  }
  exact ⟨σ, d, hσ, rfl, rfl⟩

end Erdos335.PeriodicRefinement

end
