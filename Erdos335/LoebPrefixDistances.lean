import Erdos335.LoebPrefixVectors

/-!
# Prefix distances and distances between real Loeb vectors
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Erdos335.Loeb

open Erdos335.IntermediateScale

theorem tendsto_prefixLoebVector_correlation (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f g : ℕ → ℝ)
    (hf : ∀ n, f n ∈ Icc (0 : ℝ) 1) (hg : ∀ n, g n ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun s => prefixCorrelation f g (N s)) (U : Filter ℕ)
      (𝓝 ⟪prefixLoebVector N U hU f hf, prefixLoebVector N U hU g hg⟫_ℝ) := by
  simpa only [prefixCorrelation, prefixLoebVector, Nat.card_eq_fintype_card,
    Fintype.card_fin, Finset.sum_range] using tendsto_realLoebVector_inner U hU
      (fun s (n : Fin (N s)) => f n.val) (fun s (n : Fin (N s)) => g n.val)
      (fun s n => hf n.val) (fun s n => hg n.val)

theorem tendsto_prefixLoebVector_distance (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f g : ℕ → ℝ)
    (hf : ∀ n, f n ∈ Icc (0 : ℝ) 1) (hg : ∀ n, g n ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun s => prefixEnergy (fun n => f n - g n) (N s)) (U : Filter ℕ)
      (𝓝 (‖prefixLoebVector N U hU f hf - prefixLoebVector N U hU g hg‖ ^ 2)) := by
  have hid (s : ℕ) : prefixEnergy (fun n => f n - g n) (N s) =
      prefixEnergy f (N s) + prefixEnergy g (N s) - 2 * prefixCorrelation f g (N s) := by
    have hp (n : ℕ) : (f n - g n) ^ 2 = f n ^ 2 + g n ^ 2 - 2 * (f n * g n) := by ring
    unfold prefixEnergy prefixCorrelation
    simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have h := ((tendsto_prefixLoebVector_energy N U hU f hf).add
    (tendsto_prefixLoebVector_energy N U hU g hg)).sub
      ((tendsto_prefixLoebVector_correlation N U hU f g hf hg).const_mul 2)
  have hn : ‖prefixLoebVector N U hU f hf - prefixLoebVector N U hU g hg‖ ^ 2 =
      ‖prefixLoebVector N U hU f hf‖ ^ 2 + ‖prefixLoebVector N U hU g hg‖ ^ 2 -
        2 * ⟪prefixLoebVector N U hU f hf, prefixLoebVector N U hU g hg⟫_ℝ := by
    rw [norm_sub_sq_real]
    ring
  rw [← hn] at h
  exact h.congr fun s => (hid s).symm

end Erdos335.Loeb
