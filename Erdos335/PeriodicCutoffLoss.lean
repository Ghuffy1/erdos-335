import Erdos335.IntervalPositivePart
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Translation loss after cutting a periodic function to one interval
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace Erdos335.Loeb

theorem periodic_cutoff_translation_loss_le
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hperiod : Function.Periodic f 1)
    (hnonneg : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (∫ x in 0..1, max ((Ioo (0 : ℝ) 1).indicator f x -
      (Ioo (0 : ℝ) 1).indicator f (x + t)) 0) ≤
      (∫ x in 0..1, max (f x - f (x + t)) 0) + ∫ x in 0..t, f x := by
  let g : ℝ → ℝ := (Ioo 0 1).indicator f
  let r : ℝ := 1 - t
  let k : ℝ → ℝ := (Icc r 1).indicator (fun x => f (x + t))
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hg : LocallyIntegrable g volume := hf.indicator measurableSet_Ioo
  have hi (F : ℝ → ℝ) (hF : LocallyIntegrable F volume) (a b : ℝ) :
      IntervalIntegrable F volume a b := intervalIntegrable_iff.mpr
        ((hF.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hshift (F : ℝ → ℝ) (hF : LocallyIntegrable F volume) :
      IntervalIntegrable (fun x => F (x + t)) volume 0 1 :=
    (IntervalIntegrable.comp_add_right_iff (f := F) (a := 0) (b := 1) (c := t)).mpr
      (hi F hF (0 + t) (1 + t))
  have hlossf : IntervalIntegrable (fun x => max (f x - f (x + t)) 0) volume 0 1 := by
    have h := (hi f hf 0 1).sub (hshift f hf)
    exact ⟨h.1.pos_part, h.2.pos_part⟩
  have hlossg : IntervalIntegrable (fun x => max (g x - g (x + t)) 0) volume 0 1 := by
    have h := (hi g hg 0 1).sub (hshift g hg)
    exact ⟨h.1.pos_part, h.2.pos_part⟩
  have hk : IntervalIntegrable k volume 0 1 :=
    ⟨(hshift f hf).1.indicator measurableSet_Icc, (hshift f hf).2.indicator measurableSet_Icc⟩
  have hgnonneg (x : ℝ) : 0 ≤ g x := by
    by_cases hx : x ∈ Ioo (0 : ℝ) 1 <;> simp [g, hx, hnonneg]
  have hknonneg (x : ℝ) : 0 ≤ k x := by
    by_cases hx : x ∈ Icc r 1 <;> simp [k, hx, hnonneg]
  have hpoint (x : ℝ) (hx01 : x ∈ Icc (0 : ℝ) 1) :
      max (g x - g (x + t)) 0 ≤ max (f x - f (x + t)) 0 + k x := by
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · by_cases hxt : x + t ∈ Ioo (0 : ℝ) 1
      · simp only [g, indicator_of_mem hx, indicator_of_mem hxt]
        exact le_add_of_nonneg_right (hknonneg x)
      · have hxtge : 1 ≤ x + t := by
          by_contra hn
          exact hxt ⟨by linarith [hx.1], lt_of_not_ge hn⟩
        have hxr : x ∈ Icc r 1 := ⟨by dsimp [r]; linarith, hx01.2⟩
        simp only [g, indicator_of_mem hx, indicator_of_notMem hxt, sub_zero,
          k, indicator_of_mem hxr, max_eq_left (hnonneg x)]
        linarith [le_max_left (f x - f (x + t)) (0 : ℝ)]
    · have hnonpos : g x - g (x + t) ≤ 0 := by
        simpa only [g, indicator_of_notMem hx, zero_sub] using neg_nonpos.mpr (hgnonneg (x + t))
      rw [max_eq_right hnonpos]
      exact add_nonneg (le_max_right _ _) (hknonneg x)
  have hle := intervalIntegral.integral_mono_on zero_le_one hlossg (hlossf.add hk) hpoint
  rw [intervalIntegral.integral_add hlossf hk] at hle
  have hboundary : (∫ x in 0..1, k x) = ∫ x in 0..t, f x := by
    have hsub : Icc r 1 ⊆ Ioc (0 : ℝ) 1 := fun x hx => ⟨hr.trans_le hx.1, hx.2⟩
    calc
      (∫ x in 0..1, k x) = ∫ x in Icc r 1, f (x + t) := by
        rw [intervalIntegral.integral_of_le zero_le_one]
        dsimp [k]
        rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
        rw [inter_eq_left.mpr hsub]
      _ = ∫ x in r..1, f (x + t) := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hr1]
      _ = ∫ x in 1..1 + t, f x := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 1
        dsimp [r]
        ring
      _ = ∫ x in 0..t, f (x + 1) := by
        rw [intervalIntegral.integral_comp_add_right]
        simp only [zero_add, add_comm t 1]
      _ = ∫ x in 0..t, f x := by
        congr 1
        funext x
        exact hperiod x
  rw [hboundary] at hle
  exact hle

end Erdos335.Loeb
