import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Positive functions on a measurable factor

Conditional expectation onto the pullback sigma algebra gives a bounded
measurable function on the factor. Its positive support contains the original
positive support up to a null set, and its integral is preserved. The proof
uses Mathlib's conditional expectation and Doob-Dynkin theorems.
-/

set_option autoImplicit false

open Filter Set MeasureTheory

namespace Erdos335.Loeb

theorem positive_support_condExp
    {A : Type*} {m m₀ : MeasurableSpace A} (μ : @Measure A m₀)
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (f : A → ℝ) (hf : Integrable f μ) (hnonneg : 0 ≤ᵐ[μ] f) :
    ∀ᵐ x ∂μ, 0 < f x → 0 < μ[f | m] x := by
  let Z : Set A := {x | μ[f | m] x = 0}
  have hZm : MeasurableSet[m] Z :=
    (stronglyMeasurable_condExp (μ := μ) (m := m) (f := f)).measurable (measurableSet_singleton 0)
  have hZ : MeasurableSet[m₀] Z := hm Z hZm
  have hzero : (∫ x in Z, f x ∂μ) = 0 := by
    rw [← setIntegral_condExp hm hf hZm]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact hx
  have hzero_ae : ∀ᵐ x ∂μ, x ∈ Z → f x = 0 := by
    apply (ae_restrict_iff' hZ).mp
    exact (integral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_ae hnonneg) hf.integrableOn).mp hzero
  filter_upwards [condExp_nonneg (m := m) hnonneg, hzero_ae] with x hx hz hfx
  apply lt_of_le_of_ne hx
  intro heq
  have hfzero := hz heq.symm
  linarith

theorem exists_unitInterval_conditional_factor
    {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure A) [IsFiniteMeasure μ] (q : A → B) (hq : Measurable q)
    (f : A → ℝ) (hf : Integrable f μ)
    (hbound : ∀ᵐ x ∂μ, f x ∈ Icc (0 : ℝ) 1) :
    ∃ g : B → ℝ, StronglyMeasurable g ∧
      (∀ y, g y ∈ Icc (0 : ℝ) 1) ∧
      μ[f | mB.comap q] =ᵐ[μ] g ∘ q ∧
      (∀ᵐ x ∂μ, 0 < f x → 0 < g (q x)) ∧
      (∫ y, g y ∂Measure.map q μ) = ∫ x, f x ∂μ := by
  let m := mB.comap q
  have hm : m ≤ mA := hq.comap_le
  have hn : 0 ≤ᵐ[μ] f := hbound.mono (fun _ hx => hx.1)
  have hu : f ≤ᵐ[μ] fun _ => (1 : ℝ) := hbound.mono (fun _ hx => hx.2)
  have hupper : μ[f | m] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    have h := condExp_mono (m := m) hf (integrable_const (1 : ℝ)) hu
    simpa only [condExp_const hm (1 : ℝ)] using h
  obtain ⟨g, hg, heq⟩ :=
    (stronglyMeasurable_condExp (μ := μ) (m := m) (f := f)).exists_eq_measurable_comp
  let G : B → ℝ := fun y => max 0 (min 1 (g y))
  have hclamp : Continuous (fun t : ℝ => max 0 (min 1 t)) := by fun_prop
  have hG : StronglyMeasurable G := hclamp.comp_stronglyMeasurable hg
  have hGbound (y : B) : G y ∈ Icc (0 : ℝ) 1 := by
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hGq : μ[f | m] =ᵐ[μ] G ∘ q := by
    filter_upwards [condExp_nonneg (m := m) hn, hupper] with x hx hy
    change 0 ≤ μ[f | m] x at hx
    have hgx : g (q x) = μ[f | m] x := by rw [heq]; rfl
    simp only [Function.comp_apply, G, hgx, min_eq_right hy, max_eq_right hx]
  refine ⟨G, hG, hGbound, hGq, ?_, ?_⟩
  · filter_upwards [positive_support_condExp μ hm f hf hn, hGq] with x hx he
    change μ[f | m] x = G (q x) at he
    intro hpos
    rw [← he]
    exact hx hpos
  · rw [integral_map hq.aemeasurable hG.aestronglyMeasurable]
    calc
      (∫ x, G (q x) ∂μ) = ∫ x, μ[f | m] x ∂μ := integral_congr_ae hGq.symm
      _ = ∫ x, f x ∂μ := integral_condExp hm

theorem setIntegral_conditional_factor
    {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure A) [IsFiniteMeasure μ] (q : A → B) (hq : Measurable q)
    (f : A → ℝ) (hf : Integrable f μ) (g : B → ℝ) (hg : StronglyMeasurable g)
    (heq : μ[f | mB.comap q] =ᵐ[μ] g ∘ q)
    (T : Set B) (hT : MeasurableSet T) :
    (∫ y in T, g y ∂Measure.map q μ) = ∫ x in q ⁻¹' T, f x ∂μ := by
  rw [setIntegral_map hT hg.aestronglyMeasurable hq.aemeasurable]
  calc
    (∫ x in q ⁻¹' T, g (q x) ∂μ) =
        ∫ x in q ⁻¹' T, μ[f | mB.comap q] x ∂μ := by
      apply setIntegral_congr_ae (hq hT)
      exact heq.symm.mono (fun x hx _ => hx)
    _ = ∫ x in q ⁻¹' T, f x ∂μ :=
      setIntegral_condExp hq.comap_le hf ⟨T, hT, rfl⟩

end Erdos335.Loeb
