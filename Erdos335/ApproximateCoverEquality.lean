import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Equal sets in measure from common covers of asymptotically equal mass
-/

set_option autoImplicit false

open Filter Set MeasureTheory

namespace Erdos335

theorem ae_eq_of_common_approximate_covers
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (S T : Set X) (hSm : MeasurableSet S) (hTm : MeasurableSet T) (a : ℝ)
    (hS : (μ S).toReal = a) (hT : (μ T).toReal = a)
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ C : Set X,
      S ≤ᵐ[μ] C ∧ T ≤ᵐ[μ] C ∧ (μ C).toReal ≤ a + ε) : S =ᵐ[μ] T := by
  have one_direction (A B : Set X) (hBm : MeasurableSet B) (hB : (μ B).toReal = a)
      (hcovers : ∀ ε : ℝ, 0 < ε → ∃ C : Set X,
        A ≤ᵐ[μ] C ∧ B ≤ᵐ[μ] C ∧ (μ C).toReal ≤ a + ε) : A ≤ᵐ[μ] B := by
    have hdisjoint : Disjoint (A \ B) B := by
      apply Set.disjoint_left.mpr
      exact fun x hx hxb => hx.2 hxb
    have hunion : (A \ B) ∪ B = A ∪ B := by ext x; simp
    have hmeasure : μ (A ∪ B) = μ (A \ B) + μ B := by
      rw [← hunion, measure_union hdisjoint hBm]
    have hsmall (ε : ℝ) (hε : 0 < ε) : (μ (A \ B)).toReal ≤ ε := by
      obtain ⟨C, hAC, hBC, hC⟩ := hcovers ε hε
      have hUC : A ∪ B ≤ᵐ[μ] C := by
        filter_upwards [hAC, hBC] with x hx hy hxy
        exact hxy.elim hx hy
      have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hUC)
      rw [hmeasure, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hB] at hm
      linarith
    have hzReal : (μ (A \ B)).toReal = 0 := by
      apply le_antisymm
      · by_contra hn
        have hp : 0 < (μ (A \ B)).toReal / 2 := by linarith
        have hb := hsmall _ hp
        linarith
      · exact ENNReal.toReal_nonneg
    have hz : μ (A \ B) = 0 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.zero_ne_top).mp
      simpa only [ENNReal.toReal_zero] using hzReal
    exact ae_le_set.mpr hz
  apply Filter.EventuallyLE.antisymm
  · exact one_direction S T hTm hT hcover
  · apply one_direction T S hSm hS
    intro ε hε
    obtain ⟨C, hSC, hTC, hC⟩ := hcover ε hε
    exact ⟨C, hTC, hSC, hC⟩

end Erdos335
