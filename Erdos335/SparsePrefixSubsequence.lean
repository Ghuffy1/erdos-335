import Erdos335.SlowDiagonalSelection
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sparse prefix subsequences with negligible preceding prefixes
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem exists_sparse_prefix_subsequence (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ StrictMono (N ∘ σ) ∧
      Tendsto (fun s => (N (σ (s - 1)) : ℝ) / N (σ s)) atTop (𝓝 0) := by
  have hex (k i : ℕ) : ∃ j : ℕ, i < j ∧ (k + 2) * (N i + 1) ≤ N j := by
    exact ((eventually_gt_atTop i).and
      (hN.eventually (eventually_ge_atTop ((k + 2) * (N i + 1))))).exists
  choose next hnext using hex
  let σ : ℕ → ℕ := Nat.rec 0 (fun k i => next k i)
  have hstep (k : ℕ) : σ k < σ (k + 1) ∧
      (k + 2) * (N (σ k) + 1) ≤ N (σ (k + 1)) := hnext k (σ k)
  have hσ : StrictMono σ := strictMono_nat_of_lt_succ fun k => (hstep k).1
  have hNσ : StrictMono (N ∘ σ) := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h := (hstep k).2
    change N (σ k) < N (σ (k + 1))
    nlinarith
  have hratio (k : ℕ) : (N (σ k) : ℝ) / N (σ (k + 1)) ≤ 1 / ((k : ℝ) + 2) := by
    have hdenNat : 0 < N (σ (k + 1)) := by
      have h := (hstep k).2
      nlinarith
    have hden : (0 : ℝ) < N (σ (k + 1)) := by exact_mod_cast hdenNat
    have hbound : ((k : ℝ) + 2) * ((N (σ k) : ℝ) + 1) ≤ N (σ (k + 1)) := by
      exact_mod_cast (hstep k).2
    apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < (k : ℝ) + 2)).mpr
    nlinarith
  refine ⟨σ, hσ, hNσ, ?_⟩
  apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop 1] with s hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    add_assoc, one_add_one_eq_two] using hratio k

end Erdos335.IntermediateScale
