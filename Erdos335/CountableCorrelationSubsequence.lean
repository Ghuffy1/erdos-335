import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Common subsequences for countable collections of correlations
-/

set_option autoImplicit false

open Filter Topology Set

namespace Erdos335.IntermediateScale

theorem exists_common_bounded_correlation_subsequence {ι : Type*} [Countable ι] (f : ι → ℕ → ℝ)
    (hf : ∀ k n, f k n ∈ Icc (-1 : ℝ) 1) :
    ∃ (σ : ℕ → ℕ) (a : ι → ℝ), StrictMono σ ∧
      (∀ k, a k ∈ Icc (-1 : ℝ) 1) ∧
      ∀ k, Tendsto (fun n => f k (σ n)) atTop (𝓝 (a k)) := by
  let x : ℕ → ι → Icc (-1 : ℝ) 1 := fun n k => ⟨f k n, hf k n⟩
  obtain ⟨a, σ, hσ, hlim⟩ := CompactSpace.tendsto_subseq x
  refine ⟨σ, fun k => (a k : ℝ), hσ, fun k => (a k).property, ?_⟩
  intro k
  exact ((continuous_subtype_val.comp (continuous_apply k)).tendsto a).comp hlim

theorem exists_common_filtered_correlation_subsequence {ι : Type*} [Countable ι]
    (F : Filter ℕ) [NeBot F] (hF : F ≤ atTop) (f : ι → ℕ → ℝ) (a : ι → ℝ)
    (hlim : ∀ k, Tendsto (f k) F (𝓝 (a k))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ k, Tendsto (fun n => f k (σ n)) atTop (𝓝 (a k)) := by
  let x : ℕ → ι → ℝ := fun n k => f k n
  have hx : Tendsto x F (𝓝 a) := tendsto_pi_nhds.mpr hlim
  have hle : map x F ≤ (𝓝 a) ⊓ map x atTop := le_inf hx (map_mono hF)
  have hne : NeBot ((𝓝 a) ⊓ map x atTop) := neBot_of_le hle
  obtain ⟨σ, hσ, hσlim⟩ := subseq_tendsto_of_neBot hne
  refine ⟨σ, hσ, fun k => ?_⟩
  exact ((continuous_apply k).tendsto a).comp hσlim

end Erdos335.IntermediateScale
