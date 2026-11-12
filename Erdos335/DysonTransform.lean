import Erdos335.BlockCounting

/-!
# Dyson transforms on sets of natural numbers

The transform is the one used by Kneser in the proof of the asymptotic-density
theorem, Math. Z. 58 (1953), 459–484. Its shifted-prefix invariant is exact.
The finite-set group version is also available in Mathlib's `ETransform` file.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

def dysonLeft (A B : Set ℕ) (e : ℕ) : Set ℕ := A ∪ shift B e

def dysonRight (A B : Set ℕ) (e : ℕ) : Set ℕ := B ∩ {b | b + e ∈ A}

theorem subset_dysonLeft (A B : Set ℕ) (e : ℕ) : A ⊆ dysonLeft A B e :=
  Set.subset_union_left

theorem dysonRight_subset (A B : Set ℕ) (e : ℕ) : dysonRight A B e ⊆ B :=
  Set.inter_subset_left

theorem dyson_shift_subset (A B : Set ℕ) (e : ℕ) :
    shift (dysonRight A B e) e ⊆ dysonLeft A B e := by
  rintro n ⟨b, hb, rfl⟩
  exact Or.inl hb.2

theorem dyson_shift_eq_inter (A B : Set ℕ) (e : ℕ) :
    shift (dysonRight A B e) e = A ∩ shift B e := by
  ext n
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨hb.2, ⟨b, hb.1, rfl⟩⟩
  · rintro ⟨ha, b, hb, rfl⟩
    exact ⟨b, ⟨hb, ha⟩, rfl⟩

theorem dyson_sum_subset (A B : Set ℕ) (e : ℕ) :
    dysonLeft A B e + dysonRight A B e ⊆ A + B := by
  rintro n ⟨a, ha, b, hb, rfl⟩
  rcases ha with ha | ⟨c, hc, rfl⟩
  · exact ⟨a, ha, b, hb.1, rfl⟩
  · exact ⟨b + e, hb.2, c, hc, by dsimp only; omega⟩

theorem zero_mem_dysonLeft {A B : Set ℕ} {e : ℕ} (hA : 0 ∈ A) :
    0 ∈ dysonLeft A B e := Or.inl hA

theorem zero_mem_dysonRight {A B : Set ℕ} {e : ℕ} (he : e ∈ A) (hB : 0 ∈ B) :
    0 ∈ dysonRight A B e := ⟨hB, by simpa using he⟩

theorem prefixCount_union_add_inter (A B : Set ℕ) (N : ℕ) :
    prefixCount (A ∪ B) N + prefixCount (A ∩ B) N =
      prefixCount A N + prefixCount B N := by
  classical
  simp only [prefixCount, Set.mem_union, Set.mem_inter_iff, Finset.filter_or,
    Finset.filter_and]
  exact Finset.card_union_add_card_inter _ _

theorem prefixCount_shift (A : Set ℕ) (e N : ℕ) :
    prefixCount (shift A e) N = prefixCount A (N - e) := by
  classical
  unfold prefixCount
  symm
  apply Finset.card_bij (fun n _ => n + e)
  · intro n hn
    obtain ⟨hn, ha⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ⟨n, ha, rfl⟩⟩
    have := Finset.mem_range.mp hn
    omega
  · intro a ha b hb hab
    omega
  · intro n hn
    obtain ⟨hn, a, ha, rfl⟩ := Finset.mem_filter.mp hn
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ha⟩, rfl⟩
    have := Finset.mem_range.mp hn
    change a + e < N at this
    omega

theorem dyson_prefix_invariant (A B : Set ℕ) (e N : ℕ) :
    prefixCount (dysonLeft A B e) N + prefixCount (dysonRight A B e) (N - e) =
      prefixCount A N + prefixCount B (N - e) := by
  have h := prefixCount_union_add_inter A (shift B e) N
  rw [← dyson_shift_eq_inter A B e, prefixCount_shift, prefixCount_shift] at h
  exact h

theorem dyson_prefix_error (A B : Set ℕ) (e N : ℕ) :
    |((prefixCount (dysonLeft A B e) N : ℝ) + prefixCount (dysonRight A B e) N) -
      (prefixCount A N + prefixCount B N)| ≤ e := by
  have hinv := dyson_prefix_invariant A B e N
  have hB := prefixCount_mono B (Nat.sub_le N e)
  have hD := prefixCount_mono (dysonRight A B e) (Nat.sub_le N e)
  have hB' := prefixCount_add_le B (N - e) e
  have hD' := prefixCount_add_le (dysonRight A B e) (N - e) e
  have hN : N ≤ N - e + e := by omega
  have hB'' := prefixCount_mono B hN
  have hD'' := prefixCount_mono (dysonRight A B e) hN
  have hup : prefixCount (dysonLeft A B e) N + prefixCount (dysonRight A B e) N ≤
      prefixCount A N + prefixCount B N + e := by omega
  have hlo : prefixCount A N + prefixCount B N ≤
      prefixCount (dysonLeft A B e) N + prefixCount (dysonRight A B e) N + e := by omega
  have hup' : (prefixCount (dysonLeft A B e) N : ℝ) + prefixCount (dysonRight A B e) N ≤
      prefixCount A N + prefixCount B N + e := by exact_mod_cast hup
  have hlo' : (prefixCount A N : ℝ) + prefixCount B N ≤
      prefixCount (dysonLeft A B e) N + prefixCount (dysonRight A B e) N + e :=
    by exact_mod_cast hlo
  rw [abs_le]
  constructor <;> linarith

theorem dyson_count_error (A B : Set ℕ) (e N : ℕ) :
    |((count (dysonLeft A B e) N : ℝ) + count (dysonRight A B e) N) -
      (count A N + count B N)| ≤ e + 4 := by
  have h := dyson_prefix_error A B e N
  have h1 := prefixCount_error (dysonLeft A B e) N
  have h2 := prefixCount_error (dysonRight A B e) N
  have h3 := prefixCount_error A N
  have h4 := prefixCount_error B N
  rw [abs_le] at *
  constructor <;> linarith

theorem dyson_count_difference_tendsto (A B : Set ℕ) (e : ℕ) :
    Tendsto (fun N : ℕ =>
      (((count (dysonLeft A B e) N : ℝ) + count (dysonRight A B e) N) -
        (count A N + count B N)) / N) atTop (𝓝 0) := by
  have h := tendsto_div_of_bounded
    (fun N => ((count (dysonLeft A B e) N : ℝ) + count (dysonRight A B e) N) -
      (count A N + count B N)) 0 (e + 4)
    (fun N => by simpa using dyson_count_error A B e N)
  simpa using h

inductive DysonDerived (A B : Set ℕ) : Set ℕ → Set ℕ → Prop
  | refl : DysonDerived A B A B
  | step {C D : Set ℕ} (h : DysonDerived A B C D) (e : ℕ) (he : e ∈ C) :
      DysonDerived A B (dysonLeft C D e) (dysonRight C D e)

theorem DysonDerived.left_subset {A B C D : Set ℕ} (h : DysonDerived A B C D) : A ⊆ C := by
  induction h with
  | refl => exact Set.Subset.refl A
  | step h e he ih => exact ih.trans (subset_dysonLeft _ _ _)

theorem DysonDerived.right_subset {A B C D : Set ℕ} (h : DysonDerived A B C D) : D ⊆ B := by
  induction h with
  | refl => exact Set.Subset.refl B
  | step h e he ih => exact (dysonRight_subset _ _ _).trans ih

theorem DysonDerived.sum_subset {A B C D : Set ℕ} (h : DysonDerived A B C D) :
    C + D ⊆ A + B := by
  induction h with
  | refl => exact Set.Subset.refl _
  | step h e he ih => exact (dyson_sum_subset _ _ _).trans ih

theorem DysonDerived.zero_mem {A B C D : Set ℕ} (h : DysonDerived A B C D)
    (hA : 0 ∈ A) (hB : 0 ∈ B) : 0 ∈ C ∧ 0 ∈ D := by
  induction h with
  | refl => exact ⟨hA, hB⟩
  | step h e he ih =>
      exact ⟨zero_mem_dysonLeft ih.1, zero_mem_dysonRight he ih.2⟩

theorem DysonDerived.count_difference_tendsto {A B C D : Set ℕ}
    (h : DysonDerived A B C D) :
    Tendsto (fun N : ℕ => (((count C N : ℝ) + count D N) -
      (count A N + count B N)) / N) atTop (𝓝 0) := by
  induction h with
  | refl => simp
  | @step C D h e he ih =>
      have ht := (dyson_count_difference_tendsto C D e).add ih
      simp only [add_zero] at ht
      apply ht.congr
      intro N
      ring

theorem exists_dysonDerived_cover_finite (A B : Set ℕ) (F : Finset ℕ)
    (hF : (F : Set ℕ) ⊆ A) :
    ∃ C D : Set ℕ, DysonDerived A B C D ∧ ∀ e ∈ F, shift D e ⊆ C := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨A, B, DysonDerived.refl, by simp⟩
  | @insert e F he ih =>
      obtain ⟨C, D, h, hc⟩ := ih (fun x hx => hF (Finset.mem_insert_of_mem hx))
      have heA := hF (Finset.mem_insert_self e F)
      refine ⟨dysonLeft C D e, dysonRight C D e,
        h.step e (h.left_subset heA), ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact dyson_shift_subset C D x
      · rintro n ⟨d, hd, rfl⟩
        exact Or.inl (hc x hx ⟨d, hd.1, rfl⟩)

end Erdos335
