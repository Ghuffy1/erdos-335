import Erdos335.CompactFourierConvolution
import Erdos335.HaarTranslation
import Erdos335.CompactDysonTransform
import Mathlib.MeasureTheory.Group.AEStabilizer

/-!
# Fourier coefficients and translation periods
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped ComplexConjugate Pointwise

namespace Erdos335.Loeb

theorem integral_translate_character
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (χ : AddChar G Circle) (f : G → ℂ) (t : G) :
    (∫ x, f (t + x) * conj (χ x : ℂ) ∂μ) =
      (χ t : ℂ) * ∫ x, f x * conj (χ x : ℂ) ∂μ := by
  have hpoint (x : G) :
      f (t + x) * conj (χ x : ℂ) =
        (χ t : ℂ) * (f (t + x) * conj (χ (t + x) : ℂ)) := by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, map_mul]
    symm
    calc
      (χ t : ℂ) * (f (t + x) * (conj (χ t : ℂ) * conj (χ x : ℂ))) =
          ((χ t : ℂ) * conj (χ t : ℂ)) * (f (t + x) * conj (χ x : ℂ)) := by ring
      _ = f (t + x) * conj (χ x : ℂ) := by
        rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel]
        simp
  simp_rw [hpoint]
  rw [integral_const_mul]
  congr 1
  exact integral_add_left_eq_self (μ := μ) (fun x => f x * conj (χ x : ℂ)) t

theorem character_eq_one_of_period_and_nonzero_coefficient
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (χ : AddChar G Circle) (f : G → ℂ) (t : G)
    (hperiod : (fun x => f (t + x)) =ᵐ[μ] f)
    (hcoeff : (∫ x, f x * conj (χ x : ℂ) ∂μ) ≠ 0) : χ t = 1 := by
  have hsame : (∫ x, f (t + x) * conj (χ x : ℂ) ∂μ) =
      ∫ x, f x * conj (χ x : ℂ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hperiod] with x hx
    rw [hx]
  have hmul : (χ t : ℂ) * (∫ x, f x * conj (χ x : ℂ) ∂μ) =
      1 * (∫ x, f x * conj (χ x : ℂ) ∂μ) := by
    rw [← integral_translate_character μ χ f t, hsame, one_mul]
  exact Subtype.ext (mul_right_cancel₀ hcoeff hmul)

theorem fourier_character_trivial_on_ae_stabilizer
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (χ : AddChar G Circle) (S : Set G)
    (hcoeff : (∫ x, S.indicator (fun _ => (1 : ℂ)) x * conj (χ x : ℂ) ∂μ) ≠ 0) :
    ∀ t ∈ AddAction.aestabilizer G μ S, χ t = 1 := by
  intro t ht
  apply character_eq_one_of_period_and_nonzero_coefficient μ χ
    (S.indicator fun _ => (1 : ℂ)) t _ hcoeff
  have hneg : -t +ᵥ S =ᵐ[μ] S := (AddAction.aestabilizer G μ S).neg_mem ht
  rw [vadd_set_eq_neg_preimage] at hneg
  filter_upwards [hneg] with x hx
  change (-(-t) + x ∈ S) = (x ∈ S) at hx
  simp only [neg_neg] at hx
  by_cases hs : x ∈ S
  · simp [hs, hx.mpr hs]
  · have hts : t + x ∉ S := fun h => hs (hx.mp h)
    simp [hs, hts]

end Erdos335.Loeb
