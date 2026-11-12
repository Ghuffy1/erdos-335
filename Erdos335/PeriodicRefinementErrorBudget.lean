import Erdos335.PeriodicRefinementMacroscopicApproximation
import Erdos335.PeriodicRefinementActualMacroWindows
import Erdos335.IntermediateScale

/-!
# One countable error budget for cumulative profiles and ordinary densities
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open Erdos335.IntermediateScale
open scoped Pointwise

noncomputable section

namespace Erdos335.PeriodicRefinement

def cumulativeErrorBudget {A B : Set ℕ} {M : ℕ+} {N : ℕ → ℕ}
    (d : CompactCumulativeData A B M N) (a b : ℝ) (j n : ℕ) : ℝ :=
  (N n : ℝ) * d.error j n + prefixError A a ((j + 1) * N n) +
    prefixError B b ((j + 1) * N n) + prefixError (A + B) (a + b) ((j + 1) * N n)

theorem cumulativeErrorBudget_nonnegative
    {A B : Set ℕ} {M : ℕ+} {N : ℕ → ℕ}
    (d : CompactCumulativeData A B M N) (a b : ℝ) (j n : ℕ) :
    0 ≤ cumulativeErrorBudget d a b j n := by
  unfold cumulativeErrorBudget
  exact add_nonneg
    (add_nonneg
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (d.error_nonnegative j n))
        (prefixError_nonneg A a _)) (prefixError_nonneg B b _))
    (prefixError_nonneg (A + B) (a + b) _)

theorem cumulativeErrorBudget_sublinear
    {A B : Set ℕ} {M : ℕ+} {N : ℕ → ℕ}
    (d : CompactCumulativeData A B M N) (a b : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (hN : ∀ n, 0 < N n) (hNtop : Tendsto N atTop atTop) (j : ℕ) :
    Tendsto (fun n => cumulativeErrorBudget d a b j n / N n) atTop (𝓝 0) := by
  let m : ℕ+ := ⟨j + 1, Nat.succ_pos j⟩
  have hphysical : Tendsto (fun n => (N n : ℝ) * d.error j n / N n) atTop (𝓝 0) := by
    apply (d.error_tendsto j).congr
    intro n
    have hn : (N n : ℝ) ≠ 0 := by exact_mod_cast (hN n).ne'
    field_simp [hn]
  have hleft := (hA.prefixError_mul_tendsto_zero m).comp hNtop
  have hright := (hB.prefixError_mul_tendsto_zero m).comp hNtop
  have houtput := (hC.prefixError_mul_tendsto_zero m).comp hNtop
  have hlim := ((hphysical.add hleft).add hright).add houtput
  simpa only [cumulativeErrorBudget, add_div, m, PNat.mk_coe, Function.comp_def,
    add_zero] using hlim

theorem cumulative_error_small_of_budget_small
    {A B : Set ℕ} {M : ℕ+} {N : ℕ → ℕ}
    (d : CompactCumulativeData A B M N) (a b : ℝ) (j : ℕ)
    (H : ℕ → ℕ) (hH : ∀ n, 0 < H n)
    (hsmall : Tendsto (fun n => cumulativeErrorBudget d a b j n / H n) atTop (𝓝 0)) :
    Tendsto (fun n => d.error j n * (N n : ℝ) / H n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => div_nonneg
    (mul_nonneg (d.error_nonnegative j n) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) ?_ hsmall
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hleft := prefixError_nonneg A a ((j + 1) * N n)
  have hright := prefixError_nonneg B b ((j + 1) * N n)
  have houtput := prefixError_nonneg (A + B) (a + b) ((j + 1) * N n)
  unfold cumulativeErrorBudget
  nlinarith

theorem prefix_errors_small_of_budget_small
    {A B : Set ℕ} {M : ℕ+} {N : ℕ → ℕ}
    (d : CompactCumulativeData A B M N) (a b : ℝ) (j : ℕ)
    (H : ℕ → ℕ)
    (hsmall : Tendsto (fun n => cumulativeErrorBudget d a b j n / H n) atTop (𝓝 0)) :
    Tendsto (fun n => prefixError A a ((j + 1) * N n) / H n) atTop (𝓝 0) ∧
    Tendsto (fun n => prefixError B b ((j + 1) * N n) / H n) atTop (𝓝 0) ∧
    Tendsto (fun n => prefixError (A + B) (a + b) ((j + 1) * N n) / H n)
      atTop (𝓝 0) := by
  have transfer (f : ℕ → ℝ) (hnonnegative : ∀ n, 0 ≤ f n)
      (hbound : ∀ n, f n ≤ cumulativeErrorBudget d a b j n) :
      Tendsto (fun n => f n / H n) atTop (𝓝 0) :=
    squeeze_zero (fun n => div_nonneg (hnonnegative n) (Nat.cast_nonneg _))
      (fun n => div_le_div_of_nonneg_right (hbound n) (Nat.cast_nonneg _)) hsmall
  have hleft (n : ℕ) := prefixError_nonneg A a ((j + 1) * N n)
  have hright (n : ℕ) := prefixError_nonneg B b ((j + 1) * N n)
  have houtput (n : ℕ) := prefixError_nonneg (A + B) (a + b) ((j + 1) * N n)
  have hcumulative (n : ℕ) : 0 ≤ (N n : ℝ) * d.error j n :=
    mul_nonneg (Nat.cast_nonneg _) (d.error_nonnegative j n)
  refine ⟨transfer _ hleft ?_, transfer _ hright ?_, transfer _ houtput ?_⟩ <;>
    intro n <;> unfold cumulativeErrorBudget <;>
    linarith [hleft n, hright n, houtput n, hcumulative n]

def cumulativeApproximationOfBudget
    {A B : Set ℕ} {M : ℕ+} {N : ℕ → ℕ}
    (d : CompactCumulativeData A B M N) (a b : ℝ)
    (H : ℕ → ℕ) (hH : ∀ n, 0 < H n)
    (hsmall : ∀ j, Tendsto (fun n => cumulativeErrorBudget d a b j n / H n) atTop (𝓝 0))
    (L : ℕ+) (i : Fin 3) (r : ZMod (M : ℕ)) :
    UniformCumulativeApproximation
      {k : ℕ | k ∈ macroInput A B i ∧ (k : ZMod (M : ℕ)) = r}
      (d.curve i r) N H (L : ℕ) where
  cumulative := d.primitive i r
  agreesOnNaturals := d.primitive_grid i r
  error := d.error ((L : ℕ) - 1)
  error_small := cumulative_error_small_of_budget_small d a b ((L : ℕ) - 1) H hH
    (hsmall ((L : ℕ) - 1))
  bound := by
    apply Eventually.of_forall
    intro n t ht
    have hindex : ((L : ℕ) - 1 : ℕ) + 1 = (L : ℕ) :=
      Nat.sub_add_cancel (by have := L.pos; omega)
    have hreal : (((L : ℕ) - 1 : ℕ) : ℝ) + 1 = ((L : ℕ) : ℝ) := by
      exact_mod_cast hindex
    apply d.error_bound ((L : ℕ) - 1) n i r t
    simpa only [hreal] using ht

end Erdos335.PeriodicRefinement

end
