import Erdos335.HaarApproxSequence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Prod

/-!
# An exactly invariant representative obtained by subgroup averaging
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory

noncomputable section

namespace Erdos335.Loeb

theorem exists_exact_invariant_ae_average
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableAdd₂ G] [MeasurableAdd₂ H]
    (μ : Measure G) [IsFiniteMeasure μ]
    (ν : Measure H) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant]
    (φ : H →+ G) (hφ : Measurable φ) (f : G → ℝ) (hf : Measurable f)
    (hperiod : ∀ h : H, (fun x => f (x + φ h)) =ᵐ[μ] f) :
    ∃ g : G → ℝ, Measurable g ∧ g =ᵐ[μ] f ∧ ∀ h x, g (x + φ h) = g x := by
  let g (x : G) : ℝ := ∫ h, f (x + φ h) ∂ν
  have hgm : Measurable g :=
    (show StronglyMeasurable (fun p : G × H => f (p.1 + φ p.2)) from
      (hf.comp (measurable_fst.add (hφ.comp measurable_snd))).stronglyMeasurable).integral_prod_right'.measurable
  have heqm : MeasurableSet {p : H × G | f (p.2 + φ p.1) = f p.2} :=
    measurableSet_eq_fun (hf.comp (measurable_snd.add (hφ.comp measurable_fst)))
      (hf.comp measurable_snd)
  have hpoint : ∀ᵐ x ∂μ, ∀ᵐ h ∂ν, f (x + φ h) = f x :=
    (Measure.ae_ae_comm heqm).mp (Eventually.of_forall hperiod)
  have hgae : g =ᵐ[μ] f := by
    filter_upwards [hpoint] with x hx
    dsimp only [g]
    rw [integral_congr_ae hx]
    simp
  refine ⟨g, hgm, hgae, ?_⟩
  intro a x
  calc
    g (x + φ a) = ∫ h, f (x + φ (a + h)) ∂ν := by
      apply integral_congr_ae
      filter_upwards with h
      rw [map_add]
      congr 1
      abel
    _ = g x := integral_add_left_eq_self (μ := ν) (fun h => f (x + φ h)) a

end Erdos335.Loeb

end
