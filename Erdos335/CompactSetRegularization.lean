import Erdos335.CompactPositiveLevelRegularization

/-!
# Set representatives for positive compact convolutions

These are the measurable-set conclusions of the compact convolution
reduction. Both representatives and their sum are sigma-compact. Their
measures equal the measures of the positive supports.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

namespace Erdos335.Loeb

theorem sigmaCompact_add_measurable
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (A B : Set G) (hA : IsSigmaCompact A) (hB : IsSigmaCompact B) :
    IsSigmaCompact (A + B) ∧ MeasurableSet (A + B) := by
  rcases hA with ⟨K, hK, hKA⟩
  rcases hB with ⟨L, hL, hLB⟩
  have heq : A + B = ⋃ n, ⋃ m, K n + L m := by
    rw [← hKA, ← hLB]
    ext z
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      rcases mem_iUnion.mp hx with ⟨n, hn⟩
      rcases mem_iUnion.mp hy with ⟨m, hm⟩
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨m, ⟨x, hn, y, hm, rfl⟩⟩⟩
    · intro hz
      rcases mem_iUnion.mp hz with ⟨n, hn⟩
      rcases mem_iUnion.mp hn with ⟨m, x, hx, y, hy, he⟩
      exact ⟨x, mem_iUnion.mpr ⟨n, hx⟩, y, mem_iUnion.mpr ⟨m, hy⟩, he⟩
  rw [heq]
  exact ⟨isSigmaCompact_iUnion _ (fun n => isSigmaCompact_iUnion_of_isCompact _
    (fun m => (hK n).add (hL m))),
    MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun m => ((hK n).add (hL m)).measurableSet))⟩

theorem exists_positive_support_sigmaCompact_representatives
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsOpenPosMeasure]
    (f g : G → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf01 : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    ∃ A B : Set G, IsSigmaCompact A ∧ IsSigmaCompact B ∧
      MeasurableSet A ∧ MeasurableSet B ∧
      A ⊆ {x | 0 < f x} ∧ B ⊆ {x | 0 < g x} ∧
      μ A = μ {x | 0 < f x} ∧ μ B = μ {x | 0 < g x} ∧
      IsSigmaCompact (A + B) ∧ MeasurableSet (A + B) ∧
      A + B ⊆ {z | 0 < ∫ t, f t * g (z - t) ∂μ} := by
  obtain ⟨A₀, B₀, hA₀, hB₀, hA₀sub, hB₀sub, hA₀mass, hB₀mass, hpos⟩ :=
    exists_positive_support_representatives μ f g hf hg hf01 hg01
  obtain ⟨A, hAA₀, hAsc, hAm, hAmass⟩ := exists_full_measure_sigmaCompact_subset μ A₀ hA₀
  obtain ⟨B, hBB₀, hBsc, hBm, hBmass⟩ := exists_full_measure_sigmaCompact_subset μ B₀ hB₀
  obtain ⟨hsumsc, hsumm⟩ := sigmaCompact_add_measurable A B hAsc hBsc
  refine ⟨A, B, hAsc, hBsc, hAm, hBm, hAA₀.trans hA₀sub, hBB₀.trans hB₀sub,
    hAmass.trans hA₀mass, hBmass.trans hB₀mass, hsumsc, hsumm, ?_⟩
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact hpos x (hAA₀ hx) y (hBB₀ hy)

end Erdos335.Loeb
