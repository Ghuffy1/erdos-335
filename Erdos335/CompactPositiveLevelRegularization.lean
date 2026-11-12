import Erdos335.CompactIndicatorRegularization
import Erdos335.CompactSigmaRepresentatives

/-!
# Positive-support representatives for bounded functions

Apply the indicator result to every positive level. Removing the countable
union of exceptional sets makes all levels valid simultaneously. A common
level then supplies positive convolution for any pair of retained points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

namespace Erdos335.Loeb

theorem positive_convolution_of_positive_level
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ]
    (f g : G → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf01 : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (r : ℝ) (hr : 0 < r) (z : G)
    (hpos : 0 < ∫ t, {x | r < f x}.indicator (fun _ => (1 : ℝ)) t *
      {x | r < g x}.indicator (fun _ => (1 : ℝ)) (z - t) ∂μ) :
    0 < ∫ t, f t * g (z - t) ∂μ := by
  let C := {x | r < f x}
  let D := {x | r < g x}
  have hC : MeasurableSet C := measurableSet_lt measurable_const hf
  have hD : MeasurableSet D := measurableSet_lt measurable_const hg
  have hfi : Integrable (fun t => f t * g (z - t)) μ :=
    Integrable.of_bound (hf.mul (hg.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      1 (ae_of_all μ (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf01 t).1 (hg01 _).1)]
        exact (mul_le_mul (hf01 t).2 (hg01 _).2 (hg01 _).1 (by norm_num)).trans_eq (one_mul 1)))
  have hCi : Measurable (C.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hC
  have hDi : Measurable (D.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hD
  have hind : Integrable (fun t => C.indicator (fun _ => (1 : ℝ)) t *
      D.indicator (fun _ => (1 : ℝ)) (z - t)) μ :=
    Integrable.of_bound (hCi.mul (hDi.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      1 (ae_of_all μ (fun t => by
        rw [norm_mul]
        exact (mul_le_mul (by simpa only [Real.norm_eq_abs] using indicator_one_abs_le C t)
          (by simpa only [Real.norm_eq_abs] using indicator_one_abs_le D (z - t))
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)))
  have hpoint (t : G) : r ^ 2 * (C.indicator (fun _ => (1 : ℝ)) t *
      D.indicator (fun _ => (1 : ℝ)) (z - t)) ≤ f t * g (z - t) := by
    by_cases hc : t ∈ C <;> by_cases hd : z - t ∈ D
    · have hcf : r < f t := hc
      have hdg : r < g (z - t) := hd
      simpa [hc, hd, pow_two] using mul_le_mul hcf.le hdg.le hr.le (hf01 t).1
    · simp [hc, hd, mul_nonneg (hf01 t).1 (hg01 _).1]
    · simp [hc, hd, mul_nonneg (hf01 t).1 (hg01 _).1]
    · simp [hc, hd, mul_nonneg (hf01 t).1 (hg01 _).1]
  have hbound := integral_mono (hind.const_mul (r ^ 2)) hfi hpoint
  rw [integral_const_mul] at hbound
  exact (mul_pos (sq_pos_of_pos hr) hpos).trans_le hbound

theorem exists_positive_support_representatives
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsOpenPosMeasure]
    (f g : G → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf01 : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    ∃ A B : Set G, MeasurableSet A ∧ MeasurableSet B ∧
      A ⊆ {x | 0 < f x} ∧ B ⊆ {x | 0 < g x} ∧
      μ A = μ {x | 0 < f x} ∧ μ B = μ {x | 0 < g x} ∧
      ∀ x ∈ A, ∀ y ∈ B, 0 < ∫ t, f t * g (x + y - t) ∂μ := by
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let C (n : ℕ) := {x | r n < f x}
  let D (n : ℕ) := {x | r n < g x}
  have hC (n : ℕ) : MeasurableSet (C n) := measurableSet_lt measurable_const hf
  have hD (n : ℕ) : MeasurableSet (D n) := measurableSet_lt measurable_const hg
  choose A B hAm hBm hAC hBD hAe hBe hconv using
    (fun n => exists_full_measure_indicator_representatives μ (C n) (D n) (hC n) (hD n))
  have hAae : ∀ᵐ x ∂μ, ∀ n, x ∈ C n → x ∈ A n := by
    apply ae_all_iff.mpr
    intro n
    have heq := ae_eq_of_subset_of_measure_ge (hAC n) (hAe n).ge
      (hAm n).nullMeasurableSet (measure_ne_top μ (C n))
    exact heq.mono (fun x hx hcx => hx.mpr hcx)
  have hBae : ∀ᵐ x ∂μ, ∀ n, x ∈ D n → x ∈ B n := by
    apply ae_all_iff.mpr
    intro n
    have heq := ae_eq_of_subset_of_measure_ge (hBD n) (hBe n).ge
      (hBm n).nullMeasurableSet (measure_ne_top μ (D n))
    exact heq.mono (fun x hx hdx => hx.mpr hdx)
  let A' := {x | 0 < f x} ∩ ⋂ n, ((C n)ᶜ ∪ A n)
  let B' := {x | 0 < g x} ∩ ⋂ n, ((D n)ᶜ ∪ B n)
  have hAeq : A' =ᵐ[μ] {x | 0 < f x} := by
    filter_upwards [hAae] with x hx
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, mem_iInter.mpr (fun n => ?_)⟩
      by_cases hc : x ∈ C n
      · exact Or.inr (hx n hc)
      · exact Or.inl hc
  have hBeq : B' =ᵐ[μ] {x | 0 < g x} := by
    filter_upwards [hBae] with x hx
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, mem_iInter.mpr (fun n => ?_)⟩
      by_cases hd : x ∈ D n
      · exact Or.inr (hx n hd)
      · exact Or.inl hd
  refine ⟨A', B', (measurableSet_lt measurable_const hf).inter
    (MeasurableSet.iInter (fun n => (hC n).compl.union (hAm n))),
    (measurableSet_lt measurable_const hg).inter
    (MeasurableSet.iInter (fun n => (hD n).compl.union (hBm n))),
    inter_subset_left, inter_subset_left, measure_congr hAeq, measure_congr hBeq, ?_⟩
  intro x hx y hy
  have hrF : ∀ᶠ n in atTop, r n < f x :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds hx.1)
  have hrG : ∀ᶠ n in atTop, r n < g y :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds hy.1)
  obtain ⟨n, hnF, hnG⟩ := (hrF.and hrG).exists
  have hxA : x ∈ A n := (mem_iInter.mp hx.2 n).resolve_left (not_not.mpr hnF)
  have hyB : y ∈ B n := (mem_iInter.mp hy.2 n).resolve_left (not_not.mpr hnG)
  exact positive_convolution_of_positive_level μ f g hf hg hf01 hg01 (r n) (by dsimp [r]; positivity)
    (x + y) (hconv n x hxA y hyB)

end Erdos335.Loeb
