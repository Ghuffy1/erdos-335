import Erdos335.CommonInteriorSelection
import Mathlib.Order.Interval.Finset.Nat

/-!
# Small-error starts inside a set of positive density
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem card_initial_filter_lower (S : Finset ℕ) (N T : ℕ)
    (hS : S ⊆ range N) : S.card ≤ (S.filter (fun n => n < N - T)).card + T := by
  classical
  let R := S.filter (fun n => n < N - T)
  have hsub : S \ R ⊆ Ico (N - T) N := by
    intro n hn
    obtain ⟨hnS, hnR⟩ := mem_sdiff.mp hn
    have hnN := mem_range.mp (hS hnS)
    have hlow : N - T ≤ n := by
      by_contra h
      exact hnR (mem_filter.mpr ⟨hnS, by omega⟩)
    exact mem_Ico.mpr ⟨hlow, hnN⟩
  have hbad : (S \ R).card ≤ T := by
    have h := card_le_card hsub
    simp only [Nat.card_Ico] at h
    omega
  have hcard := card_sdiff_of_subset (filter_subset (fun n => n < N - T) S)
  change (S \ R).card = S.card - R.card at hcard
  have hR := card_le_card (filter_subset (fun n => n < N - T) S)
  change R.card ≤ S.card at hR
  change S.card ≤ R.card + T
  omega

theorem exists_small_on_dense_finset (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ range N)
    (δ : ℝ) (hδ : 0 < δ) (hcard : δ * N ≤ S.card) :
    ∃ n ∈ S, f n ≤ ((∑ j ∈ range N, f j) / N) / δ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hSc : (0 : ℝ) < S.card := (mul_pos hδ hNr).trans_le hcard
  have hSne : S.Nonempty := card_pos.mp (by exact_mod_cast hSc)
  let a := (∑ j ∈ range N, f j) / N
  have ha : 0 ≤ a := div_nonneg (sum_nonneg fun j hj => hf j) hNr.le
  have ht : (∑ j ∈ range N, f j) = (N : ℝ) * a := by dsimp [a]; field_simp
  have hratio : (N : ℝ) ≤ (S.card : ℝ) / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hsum : (∑ n ∈ S, f n) ≤ ∑ _n ∈ S, a / δ := by
    calc
      _ ≤ ∑ j ∈ range N, f j := sum_le_sum_of_subset_of_nonneg hS (fun j hj hnot => hf j)
      _ = (N : ℝ) * a := ht
      _ ≤ ((S.card : ℝ) / δ) * a := mul_le_mul_of_nonneg_right hratio ha
      _ = _ := by simp; ring
  exact exists_le_of_sum_le hSne hsum

theorem exists_small_interior_positions_in_dense_sets
    (f : ℕ → ℕ → ℝ) (hf : ∀ s n, 0 ≤ f s n)
    (N T : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (S : ℕ → Finset ℕ) (hS : ∀ s, S s ⊆ range (N s))
    (δ : ℝ) (hδ : 0 < δ)
    (hcard : ∀ᶠ s in atTop, δ ≤ ((S s).card : ℝ) / N s)
    (hT : Tendsto (fun s => (T s : ℝ) / N s) atTop (𝓝 0))
    (hmean : Tendsto (fun s => (∑ n ∈ range (N s), f s n) / N s) atTop (𝓝 0)) :
    ∃ n : ℕ → ℕ, (∀ s, n s < N s) ∧
      (∀ᶠ s in atTop, n s ∈ S s ∧ n s + T s ≤ N s) ∧
      Tendsto (fun s => f s (n s)) atTop (𝓝 0) := by
  classical
  let R : ℕ → Finset ℕ := fun s => (S s).filter (fun n => n < N s - T s)
  have hRsub (s : ℕ) : R s ⊆ range (N s) := (filter_subset _ _).trans (hS s)
  have hhalf : 0 < δ / 2 := by positivity
  have hlarge : ∀ᶠ s in atTop, (δ / 2) * N s ≤ (R s).card := by
    filter_upwards [hcard, hT.eventually (gt_mem_nhds hhalf)] with s hs ht
    have hNr : (0 : ℝ) < N s := by exact_mod_cast hN s
    have hc := (le_div_iff₀ hNr).mp hs
    have htt := (div_lt_iff₀ hNr).mp ht
    have hdrop : ((S s).card : ℝ) ≤ (R s).card + T s := by
      exact_mod_cast card_initial_filter_lower (S s) (N s) (T s) (hS s)
    linarith
  let n : ℕ → ℕ := fun s => if hs : (δ / 2) * N s ≤ (R s).card then
    (exists_small_on_dense_finset (f s) (hf s) (N s) (hN s) (R s) (hRsub s) (δ / 2) hhalf hs).choose
      else 0
  have hn (s : ℕ) (hs : (δ / 2) * N s ≤ (R s).card) : n s ∈ R s ∧
      f s (n s) ≤ ((∑ j ∈ range (N s), f s j) / N s) / (δ / 2) := by
    simpa only [n, dif_pos hs] using
      (exists_small_on_dense_finset (f s) (hf s) (N s) (hN s) (R s) (hRsub s) (δ / 2) hhalf hs).choose_spec
  refine ⟨n, ?_, ?_, ?_⟩
  · intro s
    by_cases hs : (δ / 2) * N s ≤ (R s).card
    · exact mem_range.mp (hRsub s (hn s hs).1)
    · simpa only [n, dif_neg hs] using hN s
  · filter_upwards [hlarge] with s hs
    have h := mem_filter.mp (hn s hs).1
    exact ⟨h.1, by omega⟩
  · apply squeeze_zero' (Eventually.of_forall fun s => hf s (n s))
      (hlarge.mono fun s hs => (hn s hs).2) ?_
    simpa only [zero_div] using hmean.div_const (δ / 2)

end Erdos335.IntermediateScale
