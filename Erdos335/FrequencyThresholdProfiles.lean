import Erdos335.CountableFlatScaleSelection
import Erdos335.PositiveIntermediateScales
import Erdos335.LoebUltralimit

/-!
# Monotone distribution profiles for reciprocal frequency thresholds
-/

set_option autoImplicit false

open Filter Topology Set Finset
open scoped Classical

namespace Erdos335.IntermediateScale

noncomputable def frequencyThresholdAverage (N H : ℕ) (v : ℕ → ℝ) : ℝ :=
  (((range N).filter (fun n => (H : ℝ) * |v n| ≤ 1)).card : ℝ) / N

theorem frequencyThresholdAverage_mem (N H : ℕ) (hN : 0 < N) (v : ℕ → ℝ) :
    frequencyThresholdAverage N H v ∈ Icc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by unfold frequencyThresholdAverage; positivity, ?_⟩
  apply (div_le_one hNr).mpr
  exact_mod_cast (show ((range N).filter (fun n => (H : ℝ) * |v n| ≤ 1)).card ≤ N by
    simpa only [card_range] using Finset.card_le_card (filter_subset (fun n => (H : ℝ) * |v n| ≤ 1) (range N)))

theorem frequencyThresholdAverage_antitone (N H K : ℕ) (hHK : H ≤ K) (v : ℕ → ℝ) :
    frequencyThresholdAverage N K v ≤ frequencyThresholdAverage N H v := by
  have hsub : (range N).filter (fun n => (K : ℝ) * |v n| ≤ 1) ⊆
      (range N).filter (fun n => (H : ℝ) * |v n| ≤ 1) := by
    intro n hn
    obtain ⟨hn, hprod⟩ := mem_filter.mp hn
    apply mem_filter.mpr ⟨hn, ?_⟩
    have hreal : (H : ℝ) ≤ K := by exact_mod_cast hHK
    exact (mul_le_mul_of_nonneg_right hreal (abs_nonneg _)).trans hprod
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (Nat.cast_nonneg N)

noncomputable def frequencyThresholdLimit (N H : ℕ → ℕ) [∀ s, NeZero (N s)]
    (U : Ultrafilter ℕ) (v : ℕ → ℕ → ℝ) : ℝ :=
  (((U.map (fun s => (⟨frequencyThresholdAverage (N s) (H s) (v s),
    frequencyThresholdAverage_mem (N s) (H s) (NeZero.pos _) (v s)⟩ : unitInterval))).lim : unitInterval) : ℝ)

theorem tendsto_frequencyThresholdLimit (N H : ℕ → ℕ) [∀ s, NeZero (N s)]
    (U : Ultrafilter ℕ) (v : ℕ → ℕ → ℝ) :
    Tendsto (fun s => frequencyThresholdAverage (N s) (H s) (v s)) (U : Filter ℕ)
      (𝓝 (frequencyThresholdLimit N H U v)) :=
  (continuous_subtype_val.tendsto _).comp ((U.map _).le_nhds_lim)

theorem frequencyThresholdLimit_antitone (N H K : ℕ → ℕ) [∀ s, NeZero (N s)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (v : ℕ → ℕ → ℝ)
    (hHK : ∀ᶠ s in atTop, H s ≤ K s) :
    frequencyThresholdLimit N K U v ≤ frequencyThresholdLimit N H U v := by
  have hlim := (tendsto_frequencyThresholdLimit N K U v).sub (tendsto_frequencyThresholdLimit N H U v)
  have hb : ∀ᶠ s in (U : Filter ℕ),
      frequencyThresholdAverage (N s) (K s) (v s) - frequencyThresholdAverage (N s) (H s) (v s) ≤ 0 := by
    filter_upwards [hHK.filter_mono hU] with s hs
    exact sub_nonpos.mpr (frequencyThresholdAverage_antitone (N s) (H s) (K s) hs (v s))
  exact sub_nonpos.mp (le_of_tendsto hlim hb)

theorem eventually_scale_le_of_ratio_zero (H K : ℕ → ℕ) (hK : ∀ s, 0 < K s)
    (hHK : Tendsto (fun s => (H s : ℝ) / K s) atTop (𝓝 0)) :
    ∀ᶠ s in atTop, H s ≤ K s := by
  filter_upwards [hHK.eventually (eventually_lt_nhds zero_lt_one)] with s hs
  have hKr : (0 : ℝ) < K s := by exact_mod_cast hK s
  have hlt : (H s : ℝ) < K s := (div_lt_one hKr).mp hs
  exact_mod_cast hlt.le

theorem exists_common_flat_frequency_profile
    {J : Type*} [Countable J]
    (N : ℕ → ℕ) [∀ s, NeZero (N s)] (H : BlockScaleParameter → ℕ → ℕ)
    (hH : ∀ p s, 0 < H p s)
    (hsep : ∀ p q, p < q → Tendsto (fun s => (H p s : ℝ) / H q s) atTop (𝓝 0))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (v : J → ℕ → ℕ → ℝ) :
    ∃ x : unitInterval, (x : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ ∀ j t,
      frequencyThresholdLimit N (H (toLex (x, t))) U (v j) =
        frequencyThresholdLimit N (H (toLex (x, 0))) U (v j) := by
  have hmono (j : J) (p q : BlockScaleParameter) (hpq : p ≤ q) :
      frequencyThresholdLimit N (H q) U (v j) ≤ frequencyThresholdLimit N (H p) U (v j) := by
    rcases hpq.eq_or_lt with heq | hlt
    · subst q
      exact le_rfl
    · exact frequencyThresholdLimit_antitone N (H p) (H q) U hU (v j)
        (eventually_scale_le_of_ratio_zero (H p) (H q) (hH q) (hsep p q hlt))
  apply exists_common_flat_unitInterval_family
    (fun j x t => frequencyThresholdLimit N (H (toLex (x, t))) U (v j))
  · intro j x t u htu
    exact hmono j _ _ (Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, htu⟩))
  · intro j x y hxy
    exact hmono j _ _ (Prod.Lex.toLex_le_toLex.mpr (Or.inl hxy))

end Erdos335.IntermediateScale
