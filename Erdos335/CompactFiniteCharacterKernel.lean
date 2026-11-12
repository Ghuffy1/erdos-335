import Erdos335.CompactCharacterContainer
import Erdos335.CompactFiniteFiberGroup
import Erdos335.CompactHaarProbability

/-!
# Finite character kernels from localized critical pairs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem finite_character_kernel_of_localized_critical_pairs
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [ConnectedSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (S : Set G) (hS : MeasurableSet S)
    (hperiod : ∀ t : G, t +ᵥ S =ᵐ[μ] S → t = 0)
    (φ : G →+ AddCircle (1 : ℝ)) (hφ : Continuous φ) (hne : φ ≠ 0)
    (A B : ℕ → Set G) (hBm : ∀ n, MeasurableSet (B n))
    (hBpos : ∀ n, 0 < μ (B n))
    (hsum : ∀ n, A n + B n ≤ᵐ[μ] S)
    (hmass : ∀ n, (μ S).toReal = (μ (A n)).toReal + (μ (B n)).toReal)
    (hlocal : ∀ V ∈ 𝓝 (0 : G), ∀ᶠ n in atTop, B n - B n ⊆ V) :
    Finite φ.ker := by
  classical
  have hclosed : IsClosed (φ.ker : Set G) := isClosed_eq hφ continuous_const
  have : CompactSpace φ.ker := isCompact_iff_compactSpace.mp hclosed.isCompact
  have : MeasurableAdd₂ φ.ker := ⟨by
    exact ((measurable_subtype_coe.comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk⟩
  obtain ⟨ν, hνprob, hνhaar⟩ := exists_compact_addHaar_probability φ.ker
  have : IsProbabilityMeasure ν := hνprob
  have : ν.IsAddHaarMeasure := hνhaar
  obtain ⟨C, hC, hcontainers⟩ := exists_character_invariant_containers μ S hS hperiod φ hφ hne
  have hexists (n : ℕ) := hcontainers (A n) (B n)
    (nonempty_of_measure_ne_zero (hBpos n).ne') (hsum n) (hmass n)
  choose T hTm hBT hperiodT hmassT using hexists
  exact finite_fiber_group_of_localized_containers μ ν φ.ker.subtype
    Topology.IsEmbedding.subtypeVal B T hBm hTm hBT hperiodT hBpos hlocal C hC hmassT

end Erdos335.Loeb
