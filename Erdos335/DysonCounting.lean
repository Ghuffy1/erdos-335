import Erdos335.DysonStabilization

/-!
# The zero-based counting form of Dyson's theorem

This is Proposition VII for two summands in Kneser's proof. The first count
includes zero, and the second count uses the positive integers. The proof uses
the finite sequence of transforms described in his Lemma 3.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem prefixCount_mono_set {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    prefixCount A N ≤ prefixCount B N := by
  classical
  apply Finset.card_le_card
  intro n hn
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, h (Finset.mem_filter.mp hn).2⟩

theorem count_mono_cutoff (A : Set ℕ) {M N : ℕ} (h : M ≤ N) : count A M ≤ count A N := by
  classical
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hn, hA⟩ := Finset.mem_filter.mp hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi.trans h⟩, hA⟩

theorem dysonLeft_mem_iff_of_le {A B : Set ℕ} {e r : ℕ} (he : e ∈ A) (hr : r ≤ e) :
    r ∈ dysonLeft A B e ↔ r ∈ A := by
  constructor
  · rintro (ha | ⟨b, hb, hbr⟩)
    · exact ha
    · have hre : r = e := by dsimp only at hbr; omega
      simpa only [hre] using he
  · intro h
    exact Or.inl h

theorem dyson_count0_invariant (A B : Set ℕ) (e x : ℕ) (he : e ∈ A) (hB : 0 ∈ B) :
    prefixCount (dysonLeft A B e) (x + 1) + count (dysonRight A B e) (x - e) =
      prefixCount A (x + 1) + count B (x - e) := by
  have h := dyson_prefix_invariant A B e (x + 1)
  by_cases hex : e ≤ x
  · have hindex : x + 1 - e = x - e + 1 := by omega
    have hD0 : 0 ∈ dysonRight A B e := zero_mem_dysonRight he hB
    have hD := prefixCount_succ_eq_count (dysonRight A B e) (x - e)
    have hB' := prefixCount_succ_eq_count B (x - e)
    simp only [hD0, hB, ite_true] at hD hB'
    rw [hindex, hD, hB'] at h
    omega
  · have hindex : x + 1 - e = 0 := by omega
    have hcut : x - e = 0 := by omega
    simp only [hindex, hcut, count_zero, prefixCount, Finset.range_zero,
      Finset.filter_empty, Finset.card_empty, add_zero] at h ⊢
    exact h

theorem prefixCount_translated_block_le (A : Set ℕ) (t k : ℕ)
    (hblock : ∀ a ∈ A, a ≤ k → t + a ∈ A) :
    prefixCount A t + prefixCount A (k + 1) ≤ prefixCount A (t + k + 1) := by
  classical
  let L := (Finset.range t).filter (· ∈ A)
  let R := (Finset.range (k + 1)).filter (· ∈ A)
  let T := R.image (fun a => t + a)
  have hdisj : Disjoint L T := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hnlt := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn'
    omega
  have hsub : L ∪ T ⊆ (Finset.range (t + k + 1)).filter (· ∈ A) := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · obtain ⟨hn, hA⟩ := Finset.mem_filter.mp hn
      have hnt := Finset.mem_range.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hA⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨ha, haA⟩ := Finset.mem_filter.mp ha
      have hak := Finset.mem_range.mp ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hblock a haA (by omega)⟩
  have hcard := Finset.card_le_card hsub
  have hT : T.card = R.card :=
    Finset.card_image_of_injective R (fun a b h => by omega)
  rw [Finset.card_union_of_disjoint hdisj, hT] at hcard
  exact hcard

theorem strengthen_shifted_prefix_bound (A B : Set ℕ) (α : ℝ) (k : ℕ)
    (hI : ∀ x : ℕ, α * (x + 1 : ℕ) ≤
      (prefixCount A (x + 1) : ℝ) + count B (x - k))
    (hII : ∀ b ∈ B, ∀ a ∈ A, a ≤ k → b + a ∈ A) :
    ∀ x : ℕ, α * (x + 1 : ℕ) ≤
      (prefixCount A (x + 1) : ℝ) + count B (x - (k + 1)) := by
  classical
  intro x
  by_cases hx : x ≤ k
  · simpa only [Nat.sub_eq_zero_of_le hx,
      Nat.sub_eq_zero_of_le (by omega : x ≤ k + 1), count_zero, Nat.cast_zero, add_zero]
      using hI x
  · let t := x - k
    have htpos : 0 < t := by dsimp [t]; omega
    have htx : t + k = x := by dsimp [t]; omega
    have hcut : x - (k + 1) = t - 1 := by dsimp [t]; omega
    by_cases htB : t ∈ B
    · have hbase := hI k
      simp only [Nat.sub_self, count_zero, Nat.cast_zero, add_zero] at hbase
      have hprev := hI (t - 1)
      rw [show t - 1 + 1 = t by omega] at hprev
      have hblock := prefixCount_translated_block_le A t k (fun a ha hak => hII t htB a ha hak)
      rw [htx] at hblock
      have hblockR : (prefixCount A t : ℝ) + prefixCount A (k + 1) ≤
          prefixCount A (x + 1) := by exact_mod_cast hblock
      have hmono : (count B (t - 1 - k) : ℝ) ≤ count B (t - 1) := by
        exact_mod_cast count_mono_cutoff B (Nat.sub_le (t - 1) k)
      have hindex : (x + 1 : ℕ) = t + (k + 1) := by omega
      rw [hcut, hindex]
      rw [hindex] at hblockR
      push_cast
      push_cast at hbase hprev
      nlinarith
    · have hcount : count B (x - k) = count B (x - (k + 1)) := by
        have ht : t = t - 1 + 1 := by omega
        change count B t = _
        rw [ht, count_succ]
        rw [← ht]
        simp only [htB, ite_false, add_zero]
        rw [hcut]
      simpa only [hcount] using hI x

theorem exists_dysonDerived_shifted_prefix_bound (A B : Set ℕ) (α : ℝ)
    (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hI : ∀ x : ℕ, α * (x + 1 : ℕ) ≤
      (prefixCount A (x + 1) : ℝ) + count B x) (k : ℕ) :
    ∃ C D : Set ℕ, DysonDerived A B C D ∧
      (∀ x : ℕ, α * (x + 1 : ℕ) ≤
        (prefixCount C (x + 1) : ℝ) + count D (x - k)) ∧
      (∀ d ∈ D, ∀ c ∈ C, c < k → d + c ∈ C) := by
  classical
  induction k with
  | zero => exact ⟨A, B, DysonDerived.refl, by simpa using hI, by simp⟩
  | succ k ih =>
      obtain ⟨C, D, hCD, hI, hII⟩ := ih
      by_cases hk : k ∈ C
      · let E := dysonLeft C D k
        let F := dysonRight C D k
        have hEF : DysonDerived A B E F := hCD.step k hk
        have hD0 := (hCD.zero_mem hA hB).2
        have hI' : ∀ x : ℕ, α * (x + 1 : ℕ) ≤
            (prefixCount E (x + 1) : ℝ) + count F (x - k) := by
          intro x
          have hinv := dyson_count0_invariant C D k x hk hD0
          have hinvR : (prefixCount E (x + 1) : ℝ) + count F (x - k) =
              (prefixCount C (x + 1) : ℝ) + count D (x - k) := by exact_mod_cast hinv
          rw [hinvR]
          exact hI x
        have hII' : ∀ d ∈ F, ∀ c ∈ E, c ≤ k → d + c ∈ E := by
          intro d hd c hc hck
          have hcC : c ∈ C := (dysonLeft_mem_iff_of_le hk hck).mp hc
          rcases eq_or_lt_of_le hck with rfl | hlt
          · exact Or.inl hd.2
          · exact Or.inl (hII d hd.1 c hcC hlt)
        refine ⟨E, F, hEF, strengthen_shifted_prefix_bound E F α k hI' hII', ?_⟩
        intro d hd c hc hck
        exact hII' d hd c hc (by omega)
      · have hII' : ∀ d ∈ D, ∀ c ∈ C, c ≤ k → d + c ∈ C := by
          intro d hd c hc hck
          have hlt : c < k := by
            by_contra hn
            have hceq : c = k := by omega
            exact hk (hceq ▸ hc)
          exact hII d hd c hc hlt
        refine ⟨C, D, hCD, strengthen_shifted_prefix_bound C D α k hI hII', ?_⟩
        intro d hd c hc hck
        exact hII' d hd c hc (by omega)

theorem zero_based_dyson_counting (A B : Set ℕ) (α : ℝ)
    (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hI : ∀ x : ℕ, α * (x + 1 : ℕ) ≤
      (prefixCount A (x + 1) : ℝ) + count B x) (N : ℕ) :
    α * (N + 1 : ℕ) ≤ (prefixCount (A + B) (N + 1) : ℝ) := by
  obtain ⟨C, D, hCD, hI', hII⟩ := exists_dysonDerived_shifted_prefix_bound A B α hA hB hI (N + 1)
  have hd0 := (hCD.zero_mem hA hB).2
  have hCsum : C ⊆ A + B := by
    intro c hc
    exact hCD.sum_subset ⟨c, hc, 0, hd0, by simp⟩
  have hcount : (prefixCount C (N + 1) : ℝ) ≤ prefixCount (A + B) (N + 1) := by
    exact_mod_cast prefixCount_mono_set hCsum (N + 1)
  have hN := hI' N
  simp only [Nat.sub_eq_zero_of_le (by omega : N ≤ N + 1), count_zero, Nat.cast_zero,
    add_zero] at hN
  exact hN.trans hcount

end Erdos335
