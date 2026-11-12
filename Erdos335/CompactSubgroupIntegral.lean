import Erdos335.CompactSubgroupAverage
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating the subgroup average of a bounded function
-/

set_option autoImplicit false

open Set MeasureTheory

namespace Erdos335.Loeb

theorem integral_subgroup_average
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableAdd₂ G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (ν : Measure H) [IsProbabilityMeasure ν]
    (φ : H →+ G) (hφ : Measurable φ)
    (f : G → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, (∫ h, f (x + φ h) ∂ν) ∂μ) = ∫ x, f x ∂μ := by
  have hmeas : Measurable (fun p : G × H => f (p.1 + φ p.2)) :=
    hf.comp (measurable_fst.add (hφ.comp measurable_snd))
  have hi : Integrable (fun p : G × H => f (p.1 + φ p.2)) (μ.prod ν) :=
    Integrable.of_bound hmeas.aestronglyMeasurable C (ae_of_all _ (fun p => hbound _))
  rw [integral_integral_swap hi]
  have hinner (h : H) : (∫ x, f (x + φ h) ∂μ) = ∫ x, f x ∂μ := by
    simp_rw [add_comm _ (φ h)]
    exact integral_add_left_eq_self (μ := μ) f (φ h)
  simp_rw [hinner]
  simp

end Erdos335.Loeb
