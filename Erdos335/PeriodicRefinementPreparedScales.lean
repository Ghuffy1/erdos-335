import Erdos335.PeriodicRefinementErrorBudget
import Erdos335.PeriodicRefinementCommonScales
import Erdos335.SparseScaleSubsequence

/-!
# Common intermediate scales for the three cumulative profiles
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open Erdos335.IntermediateScale
open scoped Pointwise

noncomputable section

namespace Erdos335.PeriodicRefinement

def modelEnlargement (j : ℕ) : ℕ+ := ⟨j / 2 + 1, Nat.succ_pos _⟩

def modelMoving (A B : Set ℕ) (j : ℕ) : Set ℕ := if j % 2 = 0 then A else B

def modelOther (A B : Set ℕ) (j : ℕ) : Set ℕ := if j % 2 = 0 then B else A

structure PreparedMacroScales (A B : Set ℕ) (a b : ℝ) (M : ℕ+) where
  cutoff : ℕ → ℕ
  lower : ℕ → ℕ
  upper : ℕ → ℕ
  width : ℕ → ℕ
  cutoff_positive : ∀ n, 0 < cutoff n
  cutoff_tendsto : Tendsto cutoff atTop atTop
  lower_positive : ∀ n, 0 < lower n
  upper_positive : ∀ n, 0 < upper n
  width_positive : ∀ n, 0 < width n
  width_tendsto : Tendsto width atTop atTop
  lower_width : Tendsto (fun n => (lower n : ℝ) / width n) atTop (𝓝 0)
  width_upper : Tendsto (fun n => (width n : ℝ) / upper n) atTop (𝓝 0)
  width_cutoff : Tendsto (fun n => (width n : ℝ) / cutoff n) atTop (𝓝 0)
  cumulative : CompactCumulativeData A B M cutoff
  budget_small : ∀ j, Tendsto
    (fun n => cumulativeErrorBudget cumulative a b j n / width n) atTop (𝓝 0)
  model : ∀ j, Nonempty (IntermediateFourierModel
    ((modelMoving A B j).indicator (fun _ => (1 : ℝ)))
    (fun n => (modelEnlargement j : ℕ) * cutoff n) lower upper)

theorem exists_prepared_macro_scales
    (A B : Set ℕ) (a b : ℝ) (M : ℕ+)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (hmono : Monotone N)
    (hprev : Tendsto (fun n => (N (n - 1) : ℝ) / N n) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (p : PreparedMacroScales A B a b M),
      StrictMono σ ∧ p.cutoff = N ∘ σ := by
  classical
  obtain ⟨ρ, hρ, ⟨d⟩⟩ := exists_compact_cumulative_data A B M N hNpos
  let N1 := N ∘ ρ
  have hN1pos : ∀ n, 0 < N1 n := fun n => hNpos (ρ n)
  have hN1 : Tendsto N1 atTop atTop := hN.comp hρ.tendsto_atTop
  have hN1mono : Monotone N1 := hmono.comp hρ.monotone
  have hN1prev : Tendsto (fun n => (N1 (n - 1) : ℝ) / N1 n) atTop (𝓝 0) :=
    sparse_prefix_ratio_subsequence N hmono hprev ρ hρ
  let F : ℕ → ℕ → ℝ := fun j => (modelMoving A B j).indicator (fun _ => (1 : ℝ))
  have hF : ∀ j k, F j k ∈ Icc (0 : ℝ) 1 := by
    intro j k
    by_cases hk : k ∈ modelMoving A B j <;> simp [F, hk]
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨τ, L, V, H, hτ, _, hpositive, _, hH, hLH, hHV, hHN, hbudget, hmodel⟩ :=
    exists_periodic_refinement_common_scales N1 hN1pos hN1 hN1mono hN1prev
      F modelEnlargement hF (cumulativeErrorBudget d a b)
      (fun j => cumulativeErrorBudget_sublinear d a b hA hB hC hN1pos hN1 j) U hU
  let next : PreparedMacroScales A B a b M := {
    cutoff := N1 ∘ τ
    lower := L
    upper := V
    width := H
    cutoff_positive := fun n => hN1pos (τ n)
    cutoff_tendsto := hN1.comp hτ.tendsto_atTop
    lower_positive := fun n => (hpositive n).1
    upper_positive := fun n => (hpositive n).2.1
    width_positive := fun n => (hpositive n).2.2
    width_tendsto := hH
    lower_width := hLH
    width_upper := hHV
    width_cutoff := hHN
    cumulative := d.subsequence τ hτ.tendsto_atTop
    budget_small := hbudget
    model := hmodel
  }
  exact ⟨ρ ∘ τ, next, hρ.comp hτ, rfl⟩

end Erdos335.PeriodicRefinement

end
