import Erdos335.CompactSubgroupIntegral
import Erdos335.CompactDysonTransform

/-!
# Bounding a set by its invariant container and fiber diameter
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem subgroup_fiber_measure_bound
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [MeasurableSpace H] [MeasurableAdd₂ H]
    (ν : Measure H) [ν.IsAddLeftInvariant]
    (φ : H →+ G) (B V : Set G) (hdiam : B - B ⊆ V) (x : G) :
    ν {h : H | x + φ h ∈ B} ≤ ν (φ ⁻¹' V) := by
  let E := {h : H | x + φ h ∈ B}
  by_cases hE : E.Nonempty
  · obtain ⟨h₀, hh₀⟩ := hE
    have hsub : E ⊆ h₀ +ᵥ (φ ⁻¹' V) := by
      intro h hh
      refine ⟨h - h₀, ?_, by simp [vadd_eq_add]⟩
      change φ (h - h₀) ∈ V
      rw [map_sub]
      apply hdiam
      exact ⟨x + φ h, hh, x + φ h₀, hh₀, by abel⟩
    have hmass : ν (h₀ +ᵥ (φ ⁻¹' V)) = ν (φ ⁻¹' V) := by
      rw [vadd_set_eq_neg_preimage, measure_preimage_add]
    exact (measure_mono hsub).trans_eq hmass
  · have hempty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
    change ν E ≤ _
    simp [hempty]

theorem measure_le_invariant_container_mul_fiber_diameter
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableAdd₂ G] [MeasurableAdd₂ H]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (ν : Measure H) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant]
    (φ : H →+ G) (hφ : Measurable φ)
    (B T V : Set G) (hB : MeasurableSet B) (hT : MeasurableSet T)
    (hBT : B ⊆ T) (hperiod : ∀ h : H, φ h +ᵥ T = T) (hdiam : B - B ⊆ V) :
    (μ B).toReal ≤ (μ T).toReal * (ν (φ ⁻¹' V)).toReal := by
  let E (x : G) := {h : H | x + φ h ∈ B}
  let g (x : G) := ∫ h, B.indicator (fun _ => (1 : ℝ)) (x + φ h) ∂ν
  let c := (ν (φ ⁻¹' V)).toReal
  have hEm (x : G) : MeasurableSet (E x) :=
    hB.preimage (measurable_const.add hφ)
  have hg (x : G) : g x = (ν (E x)).toReal := by
    change (∫ h, (E x).indicator (fun _ => (1 : ℝ)) h ∂ν) = _
    exact integral_indicator_one (hEm x)
  have hnonneg (x : G) : 0 ≤ g x := by
    rw [hg]
    exact ENNReal.toReal_nonneg
  have hbound (x : G) : g x ≤ T.indicator (fun _ => c) x := by
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, hg]
      exact ENNReal.toReal_mono (measure_ne_top ν _)
        (subgroup_fiber_measure_bound ν φ B V hdiam x)
    · have hempty : E x = ∅ := by
        apply subset_antisymm ?_ (empty_subset _)
        intro h hh
        change False
        apply hx
        have hmem : x ∈ φ (-h) +ᵥ T := by
          refine ⟨x + φ h, hBT hh, ?_⟩
          rw [map_neg]
          simp [vadd_eq_add]
        rwa [hperiod (-h)] at hmem
      simp only [hg, hempty, measure_empty, ENNReal.toReal_zero, Set.indicator_of_notMem hx,
        le_refl]
  have hi : Integrable (T.indicator (fun _ => c)) μ := (integrable_const c).indicator hT
  have hint := integral_mono_of_nonneg (ae_of_all μ hnonneg) hi (ae_of_all μ hbound)
  have hmassB : (∫ x, g x ∂μ) = (μ B).toReal := by
    apply (integral_subgroup_average μ ν φ hφ (B.indicator (fun _ => (1 : ℝ)))
      (measurable_const.indicator hB) 1 ?_).trans
    · exact integral_indicator_one hB
    · intro x
      by_cases hx : x ∈ B <;> simp [hx]
  have hmassT : (∫ x, T.indicator (fun _ => c) x ∂μ) = (μ T).toReal * c := by
    simpa only [smul_eq_mul, measureReal_def] using (integral_indicator_const c hT (μ := μ))
  rwa [hmassB, hmassT] at hint

end Erdos335.Loeb
