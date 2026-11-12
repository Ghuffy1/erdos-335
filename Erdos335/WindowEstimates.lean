import Erdos335.DensityLimits
import Erdos335.DysonCounting

/-!
# Prefix windows for the long-interval estimate

The count identities and minimum-prefix selection are the normalization step
in Kneser's Proposition VIII.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem prefixCount_tailShift_eq_window (A : Set ℕ) {s : ℕ} (hs : 1 ≤ s) (N : ℕ) :
    prefixCount (tailShift A s) (N + 1) + count A (s - 1) = count A (s + N) := by
  classical
  have h := prefixCount_add_tailShift A s (N + 1)
  have hleft := prefixCount_succ_eq_count A (s + N)
  have hright := prefixCount_succ_eq_count A (s - 1)
  rw [show s - 1 + 1 = s by omega] at hright
  rw [show s + (N + 1) = s + N + 1 by omega, hleft, hright] at h
  omega

theorem joint_window_lower_bound (A B : Set ℕ) (γ : ℝ) {s : ℕ} (hs : 1 ≤ s)
    (hafter : ∀ N : ℕ, s ≤ N → γ * N ≤ count A N + count B N)
    (hbefore : (count A (s - 1) : ℝ) + count B (s - 1) ≤ γ * (s - 1 : ℕ))
    (N : ℕ) :
    γ * (N + 1 : ℕ) ≤ (prefixCount (tailShift A s) (N + 1) : ℝ) +
      prefixCount (tailShift B s) (N + 1) := by
  have hA := prefixCount_tailShift_eq_window A hs N
  have hB := prefixCount_tailShift_eq_window B hs N
  have hAR : (prefixCount (tailShift A s) (N + 1) : ℝ) + count A (s - 1) =
      count A (s + N) := by exact_mod_cast hA
  have hBR : (prefixCount (tailShift B s) (N + 1) : ℝ) + count B (s - 1) =
      count B (s + N) := by exact_mod_cast hB
  have h := hafter (s + N) (by omega)
  rw [Nat.cast_sub hs, Nat.cast_one] at hbefore
  push_cast at h ⊢
  nlinarith

theorem exists_joint_window_start (A B : Set ℕ) {γ : ℝ}
    (hγ : γ < jointLowerDensity A B) :
    ∃ s : ℕ, 1 ≤ s ∧
      (∀ N : ℕ, s ≤ N → γ * N ≤ count A N + count B N) ∧
      (count A (s - 1) : ℝ) + count B (s - 1) ≤ γ * (s - 1 : ℕ) := by
  classical
  have hevent := eventually_lt_of_lt_liminf hγ (jointCount_bounded_below A B)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hevent
  let P : ℕ → Prop := fun s => 1 ≤ s ∧
    ∀ N : ℕ, s ≤ N → γ * N ≤ count A N + count B N
  have hex : ∃ s : ℕ, P s := by
    refine ⟨max 1 K, by omega, ?_⟩
    intro N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact ((lt_div_iff₀ hn).mp (hK N (by omega))).le
  let s := Nat.find hex
  obtain ⟨hs, hafter⟩ := Nat.find_spec hex
  refine ⟨s, hs, hafter, ?_⟩
  by_cases hs1 : s = 1
  · simp [hs1, count_zero]
  · by_contra hbad
    have hbefore : γ * (s - 1 : ℕ) ≤ (count A (s - 1) : ℝ) + count B (s - 1) := by
      linarith
    have hP : P (s - 1) := by
      refine ⟨by omega, ?_⟩
      intro N hN
      rcases eq_or_lt_of_le hN with rfl | hlt
      · exact hbefore
      · exact hafter N (by omega)
    exact Nat.find_min hex (by dsimp [s]; omega) hP

theorem joint_window_start_mem_left (A B : Set ℕ) (γ : ℝ) {s : ℕ}
    (hγ : 0 < γ) (hs : 1 ≤ s) (hBA : B ⊆ A)
    (hat : γ * s ≤ (count A s : ℝ) + count B s)
    (hbefore : (count A (s - 1) : ℝ) + count B (s - 1) ≤ γ * (s - 1 : ℕ)) : s ∈ A := by
  classical
  by_contra hsA
  have hsB : s ∉ B := fun hsB => hsA (hBA hsB)
  have hA := count_succ A (s - 1)
  have hB := count_succ B (s - 1)
  rw [show s - 1 + 1 = s by omega] at hA hB
  simp only [hsA, hsB, ite_false, add_zero] at hA hB
  rw [hA, hB] at hat
  rw [Nat.cast_sub hs, Nat.cast_one] at hbefore
  nlinarith

theorem prefixCount_tailShift_eq_zero_before (B : Set ℕ) {s t N : ℕ}
    (hfirst : ∀ n ∈ B, s ≤ n → t ≤ n) (hN : s + N ≤ t) :
    prefixCount (tailShift B s) N = 0 := by
  classical
  unfold prefixCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn hmem
  have hnN := Finset.mem_range.mp hn
  have hbn : n + s ∈ B := hmem
  have ht := hfirst (n + s) hbn (by omega)
  omega

theorem prefixCount_tailShift_mono_first (B : Set ℕ) {s t : ℕ} (hst : s ≤ t)
    (hfirst : ∀ n ∈ B, s ≤ n → t ≤ n) (N : ℕ) :
    prefixCount (tailShift B s) N ≤ prefixCount (tailShift B t) N := by
  classical
  apply Finset.card_le_card_of_injOn (fun n => n + s - t)
  · intro n hn
    obtain ⟨hn, hB⟩ := Finset.mem_filter.mp hn
    have hnN := Finset.mem_range.mp hn
    have hBn : n + s ∈ B := hB
    have htn := hfirst (n + s) hBn (by omega)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · change n + s - t < N
      omega
    · change n + s - t + t ∈ B
      simpa only [Nat.sub_add_cancel htn] using hBn
  · intro a ha b hb hab
    have haB : a + s ∈ B := (Finset.mem_filter.mp ha).2
    have hbB : b + s ∈ B := (Finset.mem_filter.mp hb).2
    have hat := hfirst (a + s) haB (by omega)
    have hbt := hfirst (b + s) hbB (by omega)
    change a + s - t = b + s - t at hab
    omega

theorem prefixCount_tailShift_le_count_first (B : Set ℕ) {s t : ℕ} (hst : s ≤ t)
    (ht : t ∈ B) (hfirst : ∀ n ∈ B, s ≤ n → t ≤ n) (N : ℕ) :
    prefixCount (tailShift B s) (N + 1) ≤ count (tailShift B t) N + 1 := by
  have h := prefixCount_tailShift_mono_first B hst hfirst (N + 1)
  have hz : 0 ∈ tailShift B t := by simpa [tailShift] using ht
  simpa only [prefixCount_succ_eq_count, hz, ite_true] using h

theorem window_count_after_first_lower_bound (A B : Set ℕ) (γ : ℝ) {s t : ℕ}
    (hs : 1 ≤ s) (hst : s ≤ t) (ht : t ∈ B)
    (hfirst : ∀ n ∈ B, s ≤ n → t ≤ n)
    (hafter : ∀ N : ℕ, s ≤ N → γ * N ≤ count A N + count B N)
    (hbefore : (count A (s - 1) : ℝ) + count B (s - 1) ≤ γ * (s - 1 : ℕ))
    (N : ℕ) : γ * (N + 1 : ℕ) - 1 ≤
      (prefixCount (tailShift A s) (N + 1) : ℝ) + count (tailShift B t) N := by
  have hlow := joint_window_lower_bound A B γ hs hafter hbefore N
  have hupp := prefixCount_tailShift_le_count_first B hst ht hfirst N
  have huppR : (prefixCount (tailShift B s) (N + 1) : ℝ) ≤ count (tailShift B t) N + 1 :=
    by exact_mod_cast hupp
  linarith

theorem prefixCount_full_block (A : Set ℕ) (h k : ℕ)
    (hblock : ∀ i < k, h + i ∈ A) (N : ℕ) (hN : N ≤ k) :
    prefixCount A (h + N) = prefixCount A h + N := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.add_succ, prefixCount_succ, ih (by omega)]
      simp only [hblock N (by omega), ite_true]
      omega

theorem prefixCount_full_block_lower (A : Set ℕ) (h k X : ℕ)
    (hblock : ∀ i < k, h + i ∈ A) (hX : h ≤ X) :
    prefixCount A h + min k (X - h) ≤ prefixCount A X := by
  have hfull := prefixCount_full_block A h k hblock (min k (X - h)) (min_le_left _ _)
  rw [← hfull]
  apply prefixCount_mono
  have := min_le_right k (X - h)
  omega

theorem weighted_count_bound {S X γ δ : ℝ} {k : ℕ}
    (hX : 0 ≤ X) (hk : (k : ℝ) ≤ S) (hcount : γ * X - 1 ≤ S)
    (hweight : ((k : ℝ) + 1) * δ ≤ k * γ) : δ * X ≤ S := by
  by_contra hbad
  have hbad' : S < δ * X := by linarith
  have hw := mul_le_mul_of_nonneg_right hweight hX
  have hc := mul_le_mul_of_nonneg_left (show γ * X ≤ S + 1 by linarith)
    (show (0 : ℝ) ≤ k by positivity)
  have hb := mul_lt_mul_of_pos_left hbad' (show (0 : ℝ) < k + 1 by positivity)
  nlinarith

theorem initial_segment_count_bound {S X h γ δ : ℝ}
    (hh : 0 ≤ h) (hX : h ≤ X) (hγ : δ ≤ γ) (hδ : δ ≤ 1)
    (hcount : γ * h + (X - h) ≤ S) : δ * X ≤ S := by
  have hg := mul_le_mul_of_nonneg_right hγ hh
  have hd := mul_le_mul_of_nonneg_right hδ (sub_nonneg.mpr hX)
  nlinarith

theorem after_first_window_count_bound (A B : Set ℕ) (γ δ : ℝ) {s t k : ℕ}
    (hs : 1 ≤ s) (hst : s ≤ t) (ht : t ∈ B)
    (hfirst : ∀ n ∈ B, s ≤ n → t ≤ n)
    (hafter : ∀ N : ℕ, s ≤ N → γ * N ≤ count A N + count B N)
    (hbefore : (count A (s - 1) : ℝ) + count B (s - 1) ≤ γ * (s - 1 : ℕ))
    (hblock : ∀ i < k, t + i ∈ A)
    (hγ : 0 ≤ γ) (hδγ : δ ≤ γ) (hδ : δ ≤ 1)
    (hweight : ((k : ℝ) + 1) * δ ≤ k * γ) (N : ℕ) :
    δ * (N + 1 : ℕ) ≤ (prefixCount (tailShift A s) (N + 1) : ℝ) +
      count (tailShift B t) N := by
  let h := t - s
  have hsh : s + h = t := by dsimp [h]; omega
  have hblock' : ∀ i < k, h + i ∈ tailShift A s := by
    intro i hi
    change h + i + s ∈ A
    rw [show h + i + s = t + i by omega]
    exact hblock i hi
  have hmass : γ * (h : ℝ) ≤ (prefixCount (tailShift A s) h : ℝ) := by
    rcases Nat.eq_zero_or_pos h with hh | hh
    · simp [hh, prefixCount]
    · have hw := joint_window_lower_bound A B γ hs hafter hbefore (h - 1)
      rw [show h - 1 + 1 = h by omega,
        prefixCount_tailShift_eq_zero_before B hfirst (by omega : s + h ≤ t),
        Nat.cast_zero, add_zero] at hw
      exact hw
  have hcommon := window_count_after_first_lower_bound A B γ hs hst ht hfirst hafter hbefore N
  have hnonneg : (0 : ℝ) ≤ count (tailShift B t) N := by positivity
  by_cases hN : N + 1 ≤ h
  · have hw := joint_window_lower_bound A B γ hs hafter hbefore N
    rw [prefixCount_tailShift_eq_zero_before B hfirst (by omega : s + (N + 1) ≤ t),
      Nat.cast_zero, add_zero] at hw
    have hd := mul_le_mul_of_nonneg_right hδγ (show (0 : ℝ) ≤ (N + 1 : ℕ) by positivity)
    linarith
  · have hNh : h ≤ N + 1 := by omega
    have hblocks := prefixCount_full_block_lower (tailShift A s) h k (N + 1) hblock' hNh
    have hblocksR : (prefixCount (tailShift A s) h : ℝ) + (min k (N + 1 - h) : ℕ) ≤
        prefixCount (tailShift A s) (N + 1) := by exact_mod_cast hblocks
    by_cases hfull : k ≤ N + 1 - h
    · rw [min_eq_left hfull] at hblocksR
      have hg0 : 0 ≤ γ * (h : ℝ) := mul_nonneg hγ (Nat.cast_nonneg h)
      apply weighted_count_bound (show (0 : ℝ) ≤ (N + 1 : ℕ) by positivity) ?_ hcommon hweight
      linarith
    · rw [min_eq_right (by omega : N + 1 - h ≤ k), Nat.cast_sub hNh] at hblocksR
      apply initial_segment_count_bound (show (0 : ℝ) ≤ h by positivity)
        (by exact_mod_cast hNh) hδγ hδ
      linarith

end Erdos335
