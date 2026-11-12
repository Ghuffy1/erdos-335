import Erdos335.PrefixEnergyAlgebra
import Erdos335.AlmostMonotoneEnergy
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Mean-square Cauchy bounds from approximate orthogonality
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_distance_tendsto
    (N : ℕ → ℕ) (F : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (hA : ∀ k, Tendsto (fun s => prefixEnergy (f k) (N s)) atTop (𝓝 (A k)))
    (hB : ∀ k l, Tendsto (fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s))
      atTop (𝓝 (B k l))) (hown : ∀ k, B k k = 0) (k l : ℕ) :
    Tendsto (fun s => prefixEnergy (fun n => f l n - f k n) (N s)) atTop
      (𝓝 (A l - A k + 2 * B k l)) := by
  have h := ((hA l).sub (hA k)).add ((hB k l).const_mul 2)
  have h' := h.sub ((hB k k).const_mul 2)
  have h'' := h'.congr (fun s => (prefix_distance_energy_identity F (f k) (f l) (N s)).symm)
  simpa only [hown, mul_zero, sub_zero] using h''

theorem prefix_energy_cauchy_of_approximate_orthogonality
    (N : ℕ → ℕ) (F : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (ε : ℕ → ℝ)
    (hA : ∀ k, Tendsto (fun s => prefixEnergy (f k) (N s)) atTop (𝓝 (A k)))
    (hB : ∀ k l, Tendsto (fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s))
      atTop (𝓝 (B k l))) (hown : ∀ k, B k k = 0)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |B k l| ≤ ε k) : CauchySeq A := by
  have hbounded : BddAbove (Set.range A) := by
    refine ⟨1, ?_⟩
    rintro a ⟨k, rfl⟩
    exact le_of_tendsto' (hA k) (fun s => prefixEnergy_le_one (f k) (hf k) (N s))
  apply cauchy_of_almost_monotone A (fun k => 2 * ε k) hbounded
    (by simpa using hε.const_mul 2)
  intro k l hkl
  have hlimit := prefix_distance_tendsto N F f A B hA hB hown k l
  have hnonneg := ge_of_tendsto' hlimit
    (fun s => prefixEnergy_nonneg (fun n => f l n - f k n) (N s))
  have hupper := (le_abs_self (B k l)).trans (hcross k l hkl)
  linarith

theorem exists_vanishing_prefix_cauchy_bound
    (N : ℕ → ℕ) (F : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (ε : ℕ → ℝ)
    (hA : ∀ k, Tendsto (fun s => prefixEnergy (f k) (N s)) atTop (𝓝 (A k)))
    (hB : ∀ k l, Tendsto (fun s => prefixCorrelation (f k) (fun n => F n - f l n) (N s))
      atTop (𝓝 (B k l))) (hown : ∀ k, B k k = 0)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |B k l| ≤ ε k) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ l k, k ≤ l → ∀ᶠ s in atTop,
        prefixEnergy (fun n => f l n - f k n) (N s) ≤ δ k := by
  have hC := prefix_energy_cauchy_of_approximate_orthogonality N F f hf A B ε hA hB hown hε hcross
  obtain ⟨b, _, hbound, hb⟩ := cauchySeq_iff_le_tendsto_0.mp hC
  let δ := fun k => b k + 2 * ε k + 1 / ((k : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hb.add (hε.const_mul 2)).add
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨δ, hδ, fun l k hkl => ?_⟩
  have hdiff : A l - A k ≤ b k := by
    apply (le_abs_self _).trans
    simpa only [Real.dist_eq] using hbound l k k hkl le_rfl
  have hupper := (le_abs_self (B k l)).trans (hcross k l hkl)
  have hstrict : A l - A k + 2 * B k l < δ k := by
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    dsimp [δ]
    linarith
  exact ((prefix_distance_tendsto N F f A B hA hB hown k l).eventually
    (eventually_lt_nhds hstrict)).mono fun s hs => hs.le

end Erdos335.IntermediateScale
