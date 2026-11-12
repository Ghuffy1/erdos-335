import Erdos335.BlockCounting
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Continuous cumulative counts for the periodic-summand refinement

The extension agrees with the literal half-open prefix counts at every natural
integer.  Its Lipschitz bound supplies a uniform, explicit interpolation error.
-/

set_option autoImplicit false

open Filter Set Topology

noncomputable section

namespace Erdos335.PeriodicRefinement

theorem prefixCount_dist_le (S : Set ℕ) (m n : ℕ) :
    dist (prefixCount S m : ℝ) (prefixCount S n : ℝ) ≤ dist (m : ℝ) (n : ℝ) := by
  rcases le_total m n with hmn | hnm
  · have hcount := prefixCount_mono S hmn
    have hbound := prefixCount_add_le S m (n - m)
    rw [Nat.add_sub_of_le hmn] at hbound
    have hcountR : (prefixCount S m : ℝ) ≤ prefixCount S n := by exact_mod_cast hcount
    have hboundR : (prefixCount S n : ℝ) ≤ (prefixCount S m : ℝ) + (n - m : ℕ) := by
      exact_mod_cast hbound
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hcountR),
      abs_of_nonpos (sub_nonpos.mpr hmnR)]
    rw [Nat.cast_sub hmn] at hboundR
    linarith
  · have hcount := prefixCount_mono S hnm
    have hbound := prefixCount_add_le S n (m - n)
    rw [Nat.add_sub_of_le hnm] at hbound
    have hcountR : (prefixCount S n : ℝ) ≤ prefixCount S m := by exact_mod_cast hcount
    have hboundR : (prefixCount S m : ℝ) ≤ (prefixCount S n : ℝ) + (m - n : ℕ) := by
      exact_mod_cast hbound
    have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hcountR),
      abs_of_nonneg (sub_nonneg.mpr hnmR)]
    rw [Nat.cast_sub hnm] at hboundR
    linarith

theorem exists_continuous_prefix_count (S : Set ℕ) :
    ∃ G : ℝ → ℝ, LipschitzWith 1 G ∧
      (∀ n : ℕ, G n = prefixCount S n) ∧ G 0 = 0 := by
  let f : ℝ → ℝ := fun x => prefixCount S (Nat.floor x)
  have hf : LipschitzOnWith 1 f (Set.range fun n : ℕ => (n : ℝ)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    simpa [f] using prefixCount_dist_le S m n
  obtain ⟨G, hG, heq⟩ := hf.extend_real
  refine ⟨G, hG, ?_, ?_⟩
  · intro n
    simpa [f] using (heq (Set.mem_range_self n)).symm
  · simpa [f, prefixCount] using (heq (Set.mem_range_self (0 : ℕ))).symm

theorem continuous_prefix_count_error
    (S : Set ℕ) (G : ℝ → ℝ) (hG : LipschitzWith 1 G)
    (hgrid : ∀ n : ℕ, G n = prefixCount S n) (x : ℝ) (hx : 0 ≤ x) :
    |G x - (prefixCount S (Nat.floor x) : ℝ)| ≤ 1 := by
  have hdist := hG.dist_le_mul x (Nat.floor x : ℝ)
  rw [hgrid, Real.dist_eq, Real.dist_eq] at hdist
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one x
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)] at hdist
  simp only [NNReal.coe_one, one_mul] at hdist
  linarith

theorem rescaled_prefix_count_error
    (S : Set ℕ) (G : ℝ → ℝ) (hG : LipschitzWith 1 G)
    (hgrid : ∀ n : ℕ, G n = prefixCount S n)
    (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) :
    |G (t * N) / N - (prefixCount S (Nat.floor (t * N)) : ℝ) / N| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← sub_div, abs_div, abs_of_pos hNr]
  exact div_le_div_of_nonneg_right
    (continuous_prefix_count_error S G hG hgrid (t * N)
      (mul_nonneg ht (Nat.cast_nonneg N))) hNr.le

theorem rescaled_prefix_count_lipschitz
    (G : ℝ → ℝ) (hG : LipschitzWith 1 G) (N : ℕ) (hN : 0 < N) :
    LipschitzWith 1 (fun t : ℝ => G (t * N) / N) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := hG.dist_le_mul (x * N) (y * N)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h ⊢
  rw [← sub_div, abs_div, abs_of_pos hNr]
  rw [← sub_mul, abs_mul, abs_of_pos hNr] at h
  exact (div_le_iff₀ hNr).mpr h

end Erdos335.PeriodicRefinement

end
