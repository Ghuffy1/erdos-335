import Erdos335.WindowEstimates
import Erdos335.DysonProgressions

/-!
# The long-interval density estimate

The right input plus a fixed initial interval lies in the left input. The
minimum-prefix normalization and zero-based Dyson theorem then give Kneser's
Proposition VIII for two summands, including the cofinite case.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem normalized_sum_prefix_bounds (A B : Set ℕ) {k : ℕ} (hk : 0 < k)
    (hblock : ∀ b ∈ B, ∀ i < k, b + i ∈ A) (hB : B.Infinite)
    {γ δ : ℝ} (hγ : 0 < γ) (hγdensity : γ < jointLowerDensity A B)
    (hδγ : δ ≤ γ) (hδ : δ ≤ 1) (hweight : ((k : ℝ) + 1) * δ ≤ k * γ) :
    ∃ s t : ℕ, ∀ N : ℕ, δ * (N + 1 : ℕ) ≤
      (prefixCount (tailShift A s + tailShift B t) (N + 1) : ℝ) := by
  classical
  obtain ⟨s, hs, hafter, hbefore⟩ := exists_joint_window_start A B hγdensity
  have hBA : B ⊆ A := by
    intro b hb
    simpa only [add_zero] using hblock b hb 0 hk
  have hsA : s ∈ A := joint_window_start_mem_left A B γ hγ hs hBA (hafter s le_rfl) hbefore
  have hex : ∃ t : ℕ, t ∈ B ∧ s ≤ t := by
    obtain ⟨t, ht, hst⟩ := hB.exists_gt s
    exact ⟨t, ht, hst.le⟩
  let t := Nat.find hex
  obtain ⟨ht, hst⟩ := Nat.find_spec hex
  have hfirst : ∀ n ∈ B, s ≤ n → t ≤ n := by
    intro n hn hsn
    exact Nat.find_min' hex ⟨hn, hsn⟩
  have hAzero : 0 ∈ tailShift A s := by simpa [tailShift] using hsA
  have hBzero : 0 ∈ tailShift B t := by simpa [tailShift] using ht
  have hI : ∀ N : ℕ, δ * (N + 1 : ℕ) ≤
      (prefixCount (tailShift A s) (N + 1) : ℝ) + count (tailShift B t) N := by
    intro N
    exact after_first_window_count_bound A B γ δ hs hst ht hfirst hafter hbefore
      (hblock t ht) hγ.le hδγ hδ hweight N
  exact ⟨s, t, fun N => zero_based_dyson_counting _ _ δ hAzero hBzero hI N⟩

theorem lowerDensity_sum_ge_of_block_cover (A B : Set ℕ) {k : ℕ} (hk : 0 < k)
    (hblock : ∀ b ∈ B, ∀ i < k, b + i ∈ A) (hB : B.Infinite)
    {γ δ : ℝ} (hγ : 0 < γ) (hγdensity : γ < jointLowerDensity A B)
    (hδγ : δ ≤ γ) (hδ : δ ≤ 1) (hweight : ((k : ℝ) + 1) * δ ≤ k * γ) :
    δ ≤ lowerDensity (A + B) := by
  obtain ⟨s, t, hprefix⟩ := normalized_sum_prefix_bounds A B hk hblock hB hγ hγdensity
    hδγ hδ hweight
  have hall : ∀ N : ℕ, δ * N ≤ (prefixCount (tailShift A s + tailShift B t) N : ℝ) := by
    intro N
    rcases N with _ | N
    · simp [prefixCount]
    · simpa only [Nat.succ_eq_add_one] using hprefix N
  calc
    δ ≤ lowerDensity (tailShift A s + tailShift B t) := lowerDensity_ge_of_prefixCount hall
    _ = lowerDensity (shift (tailShift A s + tailShift B t) (s + t)) :=
      (lowerDensity_shift _ _).symm
    _ ≤ lowerDensity (A + B) := lowerDensity_mono (shift_tailShift_sum_subset A B s t)

theorem cofinite_sum_of_block_cover (A B : Set ℕ) {k : ℕ} (hk : 0 < k)
    (hblock : ∀ b ∈ B, ∀ i < k, b + i ∈ A) (hB : B.Infinite)
    {γ : ℝ} (hγ : 1 < γ) (hγdensity : γ < jointLowerDensity A B)
    (hweight : (k : ℝ) + 1 ≤ k * γ) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → n ∈ A + B := by
  obtain ⟨s, t, hprefix⟩ := normalized_sum_prefix_bounds A B hk hblock hB (by linarith : 0 < γ)
    hγdensity hγ.le le_rfl (by simpa only [mul_one] using hweight)
  have hall : ∀ N : ℕ, (N : ℝ) ≤ (prefixCount (tailShift A s + tailShift B t) N : ℝ) := by
    intro N
    rcases N with _ | N
    · simp [prefixCount]
    · simpa only [Nat.succ_eq_add_one, one_mul] using hprefix N
  have hfull := eq_univ_of_full_prefixCount hall
  refine ⟨s + t, ?_⟩
  intro n hn
  apply shift_tailShift_sum_subset A B s t
  refine ⟨n - (s + t), ?_, Nat.sub_add_cancel hn⟩
  rw [hfull]
  trivial

theorem lowerDensity_sum_ge_of_initial_interval (A B : Set ℕ) {k : ℕ} (hk : 0 < k)
    (hblock : ∀ i < k, i ∈ A) (hB0 : 0 ∈ B)
    {γ δ : ℝ} (hγ : 0 < γ) (hγdensity : γ < jointLowerDensity A B)
    (hδγ : δ ≤ γ) (hδ : δ ≤ 1) (hweight : ((k : ℝ) + 1) * δ ≤ k * γ) :
    δ ≤ lowerDensity (A + B) := by
  classical
  have hS : ((Finset.range k : Finset ℕ) : Set ℕ) ⊆ A := fun i hi => hblock i (Finset.mem_range.mp hi)
  obtain ⟨C, D, hCD, hcover⟩ := exists_dysonDerived_cover_finite A B (Finset.range k) hS
  have hA0 := hblock 0 hk
  have hD0 := (hCD.zero_mem hA0 hB0).2
  have hγ' : γ < jointLowerDensity C D := by rw [hCD.jointLowerDensity_eq]; exact hγdensity
  have hcover' : ∀ d ∈ D, ∀ i < k, d + i ∈ C := by
    intro d hd i hi
    exact hcover i (Finset.mem_range.mpr hi) ⟨d, hd, rfl⟩
  by_cases hD : D.Infinite
  · exact (lowerDensity_sum_ge_of_block_cover C D hk hcover' hD hγ hγ' hδγ hδ hweight).trans
      (lowerDensity_mono hCD.sum_subset)
  · have hl := lowerDensity_sum_ge_joint_of_finite_right C D hD0 (Set.not_infinite.mp hD)
    rw [hCD.jointLowerDensity_eq] at hl
    exact (hδγ.trans hγdensity.le).trans (hl.trans (lowerDensity_mono hCD.sum_subset))

theorem cofinite_sum_of_initial_interval (A B : Set ℕ) {k : ℕ} (hk : 0 < k)
    (hblock : ∀ i < k, i ∈ A) (hB0 : 0 ∈ B)
    {γ : ℝ} (hγ : 1 < γ) (hγdensity : γ < jointLowerDensity A B)
    (hweight : (k : ℝ) + 1 ≤ k * γ) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → n ∈ A + B := by
  classical
  have hS : ((Finset.range k : Finset ℕ) : Set ℕ) ⊆ A := fun i hi => hblock i (Finset.mem_range.mp hi)
  obtain ⟨C, D, hCD, hcover⟩ := exists_dysonDerived_cover_finite A B (Finset.range k) hS
  have hA0 := hblock 0 hk
  have hD0 := (hCD.zero_mem hA0 hB0).2
  have hγ' : γ < jointLowerDensity C D := by rw [hCD.jointLowerDensity_eq]; exact hγdensity
  have hcover' : ∀ d ∈ D, ∀ i < k, d + i ∈ C := by
    intro d hd i hi
    exact hcover i (Finset.mem_range.mpr hi) ⟨d, hd, rfl⟩
  have hD : D.Infinite := by
    by_contra hD
    have hl := lowerDensity_sum_ge_joint_of_finite_right C D hD0 (Set.not_infinite.mp hD)
    have hu := (lowerDensity_le_upperDensity (C + D)).trans (upperDensity_le_one (C + D))
    linarith
  obtain ⟨K, hK⟩ := cofinite_sum_of_block_cover C D hk hcover' hD hγ hγ' hweight
  exact ⟨K, fun n hn => hCD.sum_subset (hK n hn)⟩

theorem lowerDensity_sum_ge_of_interval (A B : Set ℕ) (u : ℕ) {k : ℕ} (hk : 0 < k)
    (hblock : ∀ i < k, u + i ∈ A) (hB0 : 0 ∈ B)
    {γ δ : ℝ} (hγ : 0 < γ) (hγdensity : γ < jointLowerDensity A B)
    (hδγ : δ ≤ γ) (hδ : δ ≤ 1) (hweight : ((k : ℝ) + 1) * δ ≤ k * γ) :
    δ ≤ lowerDensity (A + B) := by
  have hzero : tailShift B 0 = B := by ext n; simp [tailShift]
  have hj := jointLowerDensity_tailShift A B u 0
  rw [hzero] at hj
  have hblock' : ∀ i < k, i ∈ tailShift A u := by
    intro i hi
    simpa [tailShift, Nat.add_comm] using hblock i hi
  have hl := lowerDensity_sum_ge_of_initial_interval (tailShift A u) B hk hblock' hB0 hγ
    (by simpa only [hj] using hγdensity) hδγ hδ hweight
  have hsub := shift_tailShift_sum_subset A B u 0
  simp only [hzero, add_zero] at hsub
  calc
    δ ≤ lowerDensity (tailShift A u + B) := hl
    _ = lowerDensity (shift (tailShift A u + B) u) := (lowerDensity_shift _ _).symm
    _ ≤ lowerDensity (A + B) := lowerDensity_mono hsub

theorem cofinite_sum_of_interval (A B : Set ℕ) (u : ℕ) {k : ℕ} (hk : 0 < k)
    (hblock : ∀ i < k, u + i ∈ A) (hB0 : 0 ∈ B)
    {γ : ℝ} (hγ : 1 < γ) (hγdensity : γ < jointLowerDensity A B)
    (hweight : (k : ℝ) + 1 ≤ k * γ) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → n ∈ A + B := by
  have hzero : tailShift B 0 = B := by ext n; simp [tailShift]
  have hj := jointLowerDensity_tailShift A B u 0
  rw [hzero] at hj
  have hblock' : ∀ i < k, i ∈ tailShift A u := by
    intro i hi
    simpa [tailShift, Nat.add_comm] using hblock i hi
  obtain ⟨K, hK⟩ := cofinite_sum_of_initial_interval (tailShift A u) B hk hblock' hB0 hγ
    (by simpa only [hj] using hγdensity) hweight
  have hsub := shift_tailShift_sum_subset A B u 0
  simp only [hzero, add_zero] at hsub
  refine ⟨K + u, ?_⟩
  intro n hn
  exact hsub ⟨n - u, hK (n - u) (by omega), Nat.sub_add_cancel (by omega)⟩

theorem lowerDensity_sum_ge_min_of_long_derived_intervals (A B : Set ℕ)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hintervals : ∀ k : ℕ, 0 < k → ∃ (C D : Set ℕ) (u : ℕ),
      DysonDerived A B C D ∧ ∀ i < k, u + i ∈ C) :
    min 1 (jointLowerDensity A B) ≤ lowerDensity (A + B) := by
  by_contra hbad
  have hc : lowerDensity (A + B) < min 1 (jointLowerDensity A B) := lt_of_not_ge hbad
  obtain ⟨δ, hcδ, hδmin⟩ := exists_between hc
  have hδpos : 0 < δ := (lowerDensity_nonneg (A + B)).trans_lt hcδ
  have hδs : δ < jointLowerDensity A B := hδmin.trans_le (min_le_right _ _)
  obtain ⟨γ, hδγ, hγs⟩ := exists_between hδs
  have hdiff : 0 < γ - δ := sub_pos.mpr hδγ
  obtain ⟨k, hk⟩ := exists_nat_gt (δ / (γ - δ) + 1)
  have hfrac0 : 0 ≤ δ / (γ - δ) := div_nonneg hδpos.le hdiff.le
  have hkR : (0 : ℝ) < k := by linarith
  have hkpos : 0 < k := by exact_mod_cast hkR
  have hfrac : δ / (γ - δ) < (k : ℝ) := by linarith
  have hmul := (div_lt_iff₀ hdiff).mp hfrac
  have hweight : ((k : ℝ) + 1) * δ ≤ k * γ := by nlinarith
  obtain ⟨C, D, u, hCD, hblock⟩ := hintervals k hkpos
  have hD0 := (hCD.zero_mem hA0 hB0).2
  have hγ' : γ < jointLowerDensity C D := by rw [hCD.jointLowerDensity_eq]; exact hγs
  have hl := lowerDensity_sum_ge_of_interval C D u hkpos hblock hD0
    (hδpos.trans hδγ) hγ' hδγ.le (hδmin.trans_le (min_le_left _ _)).le hweight
  have hl' := hl.trans (lowerDensity_mono hCD.sum_subset)
  exact hcδ.not_ge hl'

theorem cofinite_sum_of_long_derived_intervals (A B : Set ℕ)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hmass : 1 < jointLowerDensity A B)
    (hintervals : ∀ k : ℕ, 0 < k → ∃ (C D : Set ℕ) (u : ℕ),
      DysonDerived A B C D ∧ ∀ i < k, u + i ∈ C) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → n ∈ A + B := by
  obtain ⟨γ, hγ, hγs⟩ := exists_between hmass
  have hdiff : 0 < γ - 1 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (γ - 1) + 1)
  have hfrac0 : 0 ≤ 1 / (γ - 1) := by positivity
  have hkR : (0 : ℝ) < k := by linarith
  have hkpos : 0 < k := by exact_mod_cast hkR
  have hfrac : 1 / (γ - 1) < (k : ℝ) := by linarith
  have hmul := (div_lt_iff₀ hdiff).mp hfrac
  have hweight : (k : ℝ) + 1 ≤ k * γ := by nlinarith
  obtain ⟨C, D, u, hCD, hblock⟩ := hintervals k hkpos
  have hD0 := (hCD.zero_mem hA0 hB0).2
  have hγ' : γ < jointLowerDensity C D := by rw [hCD.jointLowerDensity_eq]; exact hγs
  obtain ⟨K, hK⟩ := cofinite_sum_of_interval C D u hkpos hblock hD0 hγ hγ' hweight
  exact ⟨K, fun n hn => hCD.sum_subset (hK n hn)⟩

theorem stable_gcd_one_alternative (A B : Set ℕ) (q : ℕ+)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hgcd : Nat.setGcd B = 1)
    (hstable : ∀ C D : Set ℕ, DysonDerived A B C D →
      HasGap D q ∧ Nat.setGcd D = Nat.setGcd B ∧
        residues (q : ℕ) D = residues (q : ℕ) B) :
    jointLowerDensity A B ≤ lowerDensity (A + B) ∨
      ∃ K : ℕ, ∀ n : ℕ, K ≤ n → n ∈ A + B := by
  have hg : 0 < Nat.setGcd B := by rw [hgcd]; norm_num
  have hS : (({0} : Finset ℕ) : Set ℕ) ⊆ A := by simpa using hA0
  have hintervals : ∀ k : ℕ, 0 < k → ∃ (C D : Set ℕ) (u : ℕ),
      DysonDerived A B C D ∧ ∀ i < k, u + i ∈ C := by
    intro k hk
    obtain ⟨C, D, u, hCD, hp⟩ := exists_dysonDerived_progressions A B q hg hstable {0} hS k
    refine ⟨C, D, u, hCD, ?_⟩
    intro i hi
    simpa only [zero_add, hgcd, mul_one] using hp 0 (by simp) i hi.le
  by_cases hs : jointLowerDensity A B ≤ 1
  · left
    simpa only [min_eq_right hs] using lowerDensity_sum_ge_min_of_long_derived_intervals A B hA0 hB0 hintervals
  · right
    exact cofinite_sum_of_long_derived_intervals A B hA0 hB0 (lt_of_not_ge hs) hintervals

theorem cofinite_sum_of_stable_gcd_one (A B : Set ℕ) (q : ℕ+)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hgcd : Nat.setGcd B = 1)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B)
    (hstable : ∀ C D : Set ℕ, DysonDerived A B C D →
      HasGap D q ∧ Nat.setGcd D = Nat.setGcd B ∧
        residues (q : ℕ) D = residues (q : ℕ) B) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → n ∈ A + B := by
  rcases stable_gcd_one_alternative A B q hA0 hB0 hgcd hstable with h | h
  · exact False.elim (hgap.not_ge h)
  · exact h

end Erdos335
