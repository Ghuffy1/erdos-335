import Erdos335.FrequencyBandDensity
import Erdos335.CountableCorrelationSubsequence

/-!
# Selecting a common frequency gap for countably many frequency arrays

Monotone threshold profiles and a common flat fiber give the scale
selection. The countable flat-fiber argument extends the selection
principle in Ackelsberg and Richter, Lemma 8.8.
-/

set_option autoImplicit false

open Filter Topology Set

namespace Erdos335.IntermediateScale

theorem exists_frequency_scale_selection
    {J : Type*} [Countable J]
    (N : ℕ → ℕ) [∀ s, NeZero (N s)] (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (v : J → ℕ → ℕ → ℝ) :
    ∃ (A B σ : ℕ → ℕ), StrictMono σ ∧
      (∀ s, 0 < A s ∧ 0 < B s) ∧
      Tendsto (fun s => (lower s : ℝ) / A s) atTop (𝓝 0) ∧
      Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0) ∧
      Tendsto (fun s => (B s : ℝ) / upper s) atTop (𝓝 0) ∧
      ∀ (j : J) (W : ℕ → ℕ), (∀ᶠ s in atTop, 0 < W s) →
        Tendsto (fun s => (A (σ s) : ℝ) / W s) atTop (𝓝 0) →
        Tendsto (fun s => (W s : ℝ) / B (σ s)) atTop (𝓝 0) →
        ∀ C : ℕ, 0 < C →
          Tendsto (fun s => frequencyBandDensity (N (σ s)) (W s) C (v j (σ s))) atTop (𝓝 0) := by
  obtain ⟨x, _hx, hflat⟩ := exists_common_flat_frequency_profile N (blockScaleFamily lower upper)
    (blockScaleFamily_pos lower upper) (blockScaleFamily_separated lower upper hlower hgap) U hU v
  let p : BlockScaleParameter := toLex (x, 0)
  let q : BlockScaleParameter := toLex (x, 1)
  let A := blockScaleFamily lower upper p
  let B := blockScaleFamily lower upper q
  have hApos := blockScaleFamily_pos lower upper p
  have hBpos := blockScaleFamily_pos lower upper q
  have hpq : p < q := Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, zero_lt_one⟩)
  have hAB : Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0) :=
    blockScaleFamily_separated lower upper hlower hgap p q hpq
  let T : Bool × J → ℕ → ℝ := fun j s =>
    if j.1 then frequencyThresholdAverage (N s) (B s) (v j.2 s)
    else frequencyThresholdAverage (N s) (A s) (v j.2 s)
  let t : Bool × J → ℝ := fun j =>
    if j.1 then frequencyThresholdLimit N B U (v j.2) else frequencyThresholdLimit N A U (v j.2)
  have hT : ∀ j, Tendsto (T j) (U : Filter ℕ) (𝓝 (t j)) := by
    rintro ⟨b, j⟩
    cases b
    · exact tendsto_frequencyThresholdLimit N A U (v j)
    · exact tendsto_frequencyThresholdLimit N B U (v j)
  obtain ⟨σ, hσ, hlim⟩ := exists_common_filtered_correlation_subsequence (U : Filter ℕ) hU T t hT
  refine ⟨A, B, σ, hσ, (fun s => ⟨hApos s, hBpos s⟩), ?_, hAB, ?_, ?_⟩
  · exact positiveIntermediateScale_lower_ratio lower upper hlower hgap _ _ (blockScaleExponent_mem p).1
  · exact positiveIntermediateScale_ambient_ratio lower upper upper hlower hupper hgap
      (Eventually.of_forall fun _ => le_rfl) _ _ (blockScaleExponent_mem q).1 (blockScaleExponent_mem q).2
  · intro j W hW hAW hWB C hC
    have hprofile : Tendsto (fun s => frequencyThresholdAverage (N (σ s)) (A (σ s)) (v j (σ s)) -
        frequencyThresholdAverage (N (σ s)) (B (σ s)) (v j (σ s))) atTop (𝓝 0) := by
      have heq : frequencyThresholdLimit N B U (v j) = frequencyThresholdLimit N A U (v j) := hflat j 1
      simpa [T, t, heq]
        using (hlim (false, j)).sub (hlim (true, j))
    have hab' : ∀ᶠ s in atTop, A (σ s) ≤ B (σ s) :=
      hσ.tendsto_atTop.eventually (eventually_scale_le_of_ratio_zero A B hBpos hAB)
    exact frequencyBandDensity_tendsto_zero (N ∘ σ) (A ∘ σ) (B ∘ σ) W
      (fun s => v j (σ s)) hW (fun s => hBpos (σ s)) hab' hAW hWB hprofile C hC

end Erdos335.IntermediateScale
