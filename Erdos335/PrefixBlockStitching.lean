import Erdos335.PrefixPatching
import Erdos335.SlowDiagonalSelection

/-!
# Stitching bounded approximants along growing prefixes
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

noncomputable def firstCutIndex (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (n : ℕ) : ℕ :=
  Nat.find ((hN.eventually (eventually_gt_atTop n)).exists)

theorem firstCutIndex_spec (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (n : ℕ) :
    n < N (firstCutIndex N hN n) := by
  unfold firstCutIndex
  exact Nat.find_spec ((hN.eventually (eventually_gt_atTop n)).exists)

theorem firstCutIndex_eq (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (s n : ℕ) (hhigh : n < N s) (hlow : N (s - 1) ≤ n) : firstCutIndex N hN n = s := by
  have hle : firstCutIndex N hN n ≤ s := Nat.find_min' _ hhigh
  by_contra hne
  have hlt : firstCutIndex N hN n < s := lt_of_le_of_ne hle hne
  have hprev : firstCutIndex N hN n ≤ s - 1 := by omega
  have hm := hmono hprev
  have hs := firstCutIndex_spec N hN n
  omega

noncomputable def prefixStitch (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (f : ℕ → ℕ → ℝ) (k : ℕ → ℕ) (n : ℕ) : ℝ := f (k (firstCutIndex N hN n)) n

theorem prefixStitch_bounds (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (f : ℕ → ℕ → ℝ) (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1) (k : ℕ → ℕ) (n : ℕ) :
    prefixStitch N hN f k n ∈ Set.Icc (0 : ℝ) 1 := hf _ _

theorem prefixStitch_energy_bound (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hmono : Monotone N) (f : ℕ → ℕ → ℝ) (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ → ℕ) (j s : ℕ) :
    ∑ n ∈ range (N s), (prefixStitch N hN f k n - f j n) ^ 2 ≤
      (N (s - 1) : ℝ) + ∑ n ∈ range (N s), (f (k s) n - f j n) ^ 2 := by
  apply prefix_patching_energy_bound _ _ _ _ _
    (prefixStitch_bounds N hN f hf k) (hf j)
  intro n hlow hhigh
  simp only [prefixStitch, firstCutIndex_eq N hN hmono s n hhigh hlow]

theorem exists_prefix_stitched_approximation
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (f : ℕ → ℕ → ℝ) (hf : ∀ k n, f k n ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℕ → ℝ)
    (hpair : ∀ l k, k ≤ l → ∀ᶠ s in atTop,
      (∑ n ∈ range (N s), (f l n - f k n) ^ 2) / N s ≤ ε k) :
    ∃ (k : ℕ → ℕ) (g : ℕ → ℝ), Tendsto k atTop atTop ∧
      (∀ n, g n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, g n = f (k (firstCutIndex N hN n)) n) ∧
      ∀ j, ∀ᶠ s in atTop,
        (∑ n ∈ range (N s), (g n - f j n) ^ 2) / N s ≤ ε j + (N (s - 1) : ℝ) / N s := by
  obtain ⟨k, hk, _, hgood⟩ := exists_slow_diagonal_for_finite_requirements
    (fun j l s => (∑ n ∈ range (N s), (f l n - f j n) ^ 2) / N s ≤ ε j) hpair
  let g := prefixStitch N hN f k
  refine ⟨k, g, hk, prefixStitch_bounds N hN f hf k, fun n => rfl, fun j => ?_⟩
  filter_upwards [hgood, hk.eventually (eventually_ge_atTop j)] with s hs hjs
  have henergy := prefixStitch_energy_bound N hN hmono f hf k j s
  have hdiv := div_le_div_of_nonneg_right henergy (Nat.cast_nonneg (N s) : (0 : ℝ) ≤ N s)
  rw [add_div] at hdiv
  have hclose := hs j hjs
  change (∑ n ∈ range (N s), (g n - f j n) ^ 2) / N s ≤ _ at hdiv
  linarith

end Erdos335.IntermediateScale
