import Erdos335.RemovalParameters

/-!
# Asymptotic removal from popular sumset containers

An estimate for popular sums with vanishing thresholds yields trimmed
sets whose literal sumsets satisfy a vanishing container error.
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Pointwise

noncomputable section

namespace Erdos335.ArithmeticRemoval

theorem popularSum_antitone
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (δ τ : ℝ) (hδτ : δ ≤ τ) : popularSum A B τ ⊆ popularSum A B δ := by
  classical
  intro c hc
  simp only [popularSum, mem_filter, mem_univ, true_and] at hc ⊢
  exact (mul_le_mul_of_nonneg_right hδτ (Nat.cast_nonneg _)).trans_lt hc

theorem asymptotic_sumset_removal
    {G : ℕ → Type*} [∀ n, AddCommGroup (G n)] [∀ n, Fintype (G n)] [∀ n, DecidableEq (G n)]
    (A B C : ∀ n, Finset (G n)) (δ η : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0))
    (hpopular : ∀ᶠ n in atTop,
      ((popularSum (A n) (B n) (δ n) \ C n).card : ℝ) ≤ η n * Fintype.card (G n)) :
    ∃ A' B' : ∀ n, Finset (G n),
      (∀ n, A' n ⊆ A n ∧ B' n ⊆ B n) ∧
      Tendsto (fun n => ((A n \ A' n).card : ℝ) / Fintype.card (G n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ((B n \ B' n).card : ℝ) / Fintype.card (G n)) atTop (𝓝 0) ∧
      Tendsto (fun n => (((A' n + B' n) \ C n).card : ℝ) / Fintype.card (G n)) atTop (𝓝 0) := by
  classical
  obtain ⟨ε, hεpos, hε, hthreshold⟩ := exists_vanishing_removal_parameters δ hδ
  have hex (n : ℕ) : ∃ A' ⊆ A n, ∃ B' ⊆ B n,
      (δ n ≤ popularRemovalBound (ε n) ∧
        ((popularSum (A n) (B n) (δ n) \ C n).card : ℝ) ≤ η n * Fintype.card (G n)) →
      ((A n \ A').card : ℝ) < ε n * Fintype.card (G n) ∧
      ((B n \ B').card : ℝ) < ε n * Fintype.card (G n) ∧
      (((A' + B') \ C n).card : ℝ) < (ε n + η n) * Fintype.card (G n) := by
    by_cases hn : δ n ≤ popularRemovalBound (ε n) ∧
        ((popularSum (A n) (B n) (δ n) \ C n).card : ℝ) ≤ η n * Fintype.card (G n)
    · have hbound : ((popularSum (A n) (B n) (popularRemovalBound (ε n)) \ C n).card : ℝ) ≤
          η n * Fintype.card (G n) := by
        apply le_trans ?_ hn.2
        exact_mod_cast card_le_card (Finset.sdiff_subset_sdiff
          (popularSum_antitone (A n) (B n) _ _ hn.1) (Finset.Subset.refl (C n)))
      obtain ⟨A', hA', B', hB', hbounds⟩ := popular_sumset_container (A n) (B n) (C n) (ε n) (η n)
        (hεpos n) hbound
      exact ⟨A', hA', B', hB', fun _ => hbounds⟩
    · exact ⟨∅, empty_subset _, ∅, empty_subset _, fun h => False.elim (hn h)⟩
  choose A' hA' B' hB' hbounds using hex
  have hgood : ∀ᶠ n in atTop,
      ((A n \ A' n).card : ℝ) < ε n * Fintype.card (G n) ∧
      ((B n \ B' n).card : ℝ) < ε n * Fintype.card (G n) ∧
      (((A' n + B' n) \ C n).card : ℝ) < (ε n + η n) * Fintype.card (G n) := by
    filter_upwards [hthreshold, hpopular] with n hn hp
    exact hbounds n ⟨hn, hp⟩
  have hN (n : ℕ) : (0 : ℝ) < Fintype.card (G n) := by exact_mod_cast Fintype.card_pos
  refine ⟨A', B', (fun n => ⟨hA' n, hB' n⟩), ?_, ?_, ?_⟩
  · apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hε
    exact hgood.mono (fun n hn => (div_le_iff₀ (hN n)).mpr hn.1.le)
  · apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hε
    exact hgood.mono (fun n hn => (div_le_iff₀ (hN n)).mpr hn.2.1.le)
  · have hlim : Tendsto (fun n => ε n + η n) atTop (𝓝 0) := by
      simpa only [add_zero] using hε.add hη
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
    exact hgood.mono (fun n hn => (div_le_iff₀ (hN n)).mpr hn.2.2.le)

end Erdos335.ArithmeticRemoval

end
