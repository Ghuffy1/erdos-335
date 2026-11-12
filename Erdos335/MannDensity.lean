import Erdos335.LowerDensity
import Erdos335.Upstream.Mann

/-!
# Mann's theorem in the ordinary-density interface

These bridges use the credited Mann/Dyson proof with the project's exact
positive-prefix counting convention.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem dyson_prefix_lower_bound (A B : Set ℕ) (δ : ℝ) (N : ℕ)
    (hA : 0 ∈ A) (hB : 0 ∈ B) (hδ : δ ≤ 1)
    (hprefix : ∀ m : ℕ, 1 ≤ m → m ≤ N → δ * m ≤ count A m + count B m) :
    δ * N ≤ (count (A + B) N : ℝ) := by
  classical
  let F : ℕ → Set ℕ := fun i => if i = 0 then A else B
  have hh : LeanLab.Schnirelmann.Mann.DysonHypR F 2 N δ := by
    intro m hm hmn
    simpa [LeanLab.Ramare1995.Theorem91.phi, LeanLab.Ramare1995.Section9.cnt,
      F, Finset.sum_range_succ, count] using hprefix m hm hmn
  have ht := LeanLab.Schnirelmann.Mann.dysonR 1 N F δ hδ hh
  have hsub : LeanLab.Schnirelmann.Mann.SumSet F 2 ⊆ A + B := by
    rintro n ⟨f, hf, rfl⟩
    have ha : f 0 ∈ A := by
      rcases hf 0 (by omega) with h | h
      · simpa only [h] using hA
      · simpa [F] using h
    have hb : f 1 ∈ B := by
      rcases hf 1 (by omega) with h | h
      · simpa only [h] using hB
      · simpa [F] using h
    convert Set.add_mem_add ha hb using 1
    simp [Finset.sum_range_succ]
  have hc := count_mono hsub N
  have htr : δ * N ≤ (count (LeanLab.Schnirelmann.Mann.SumSet F 2) N : ℝ) := by
    simpa only [LeanLab.Ramare1995.Section9.cnt, count] using ht
  exact htr.trans (by exact_mod_cast hc)

theorem lowerDensity_sum_ge_of_joint_prefix (A B : Set ℕ) (δ : ℝ)
    (hA : 0 ∈ A) (hB : 0 ∈ B) (hδ : δ ≤ 1)
    (hprefix : ∀ m : ℕ, 1 ≤ m → δ * m ≤ count A m + count B m) :
    δ ≤ lowerDensity (A + B) := by
  apply le_liminf_of_le (count_ratio_bounded_above (A + B)).isCobounded_flip
  filter_upwards [eventually_ge_atTop 1] with N hN
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < N by omega))).mpr
  exact dyson_prefix_lower_bound A B δ N hA hB hδ (fun m hm _ => hprefix m hm)

theorem lowerDensity_sum_ge_mann (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B) :
    min 1 (by classical exact schnirelmannDensity A + schnirelmannDensity B) ≤
      lowerDensity (A + B) := by
  classical
  apply lowerDensity_sum_ge_of_joint_prefix A B _ hA hB (min_le_left _ _)
  intro m hm
  have h1 := schnirelmannDensity_mul_le_card_filter (A := A) (n := m)
  have h2 := schnirelmannDensity_mul_le_card_filter (A := B) (n := m)
  have hh := mul_le_mul_of_nonneg_right
    (min_le_right 1 (schnirelmannDensity A + schnirelmannDensity B))
    (show (0 : ℝ) ≤ m by positivity)
  have hI : (Finset.Ioc 0 m : Finset ℕ) = Finset.Icc 1 m := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hI] at h1 h2
  change schnirelmannDensity A * m ≤ (count A m : ℝ) at h1
  change schnirelmannDensity B * m ≤ (count B m : ℝ) at h2
  nlinarith

theorem hasDensity_sum_one_of_joint_prefix (A B : Set ℕ)
    (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hprefix : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ count A m + count B m) :
    HasDensity (A + B) 1 := by
  apply hasDensity_of_lowerDensity_ge_upperDensity_le
  · apply lowerDensity_sum_ge_of_joint_prefix A B 1 hA hB le_rfl
    simpa only [one_mul] using hprefix
  · exact upperDensity_le_one (A + B)

end Erdos335
