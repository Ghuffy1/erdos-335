import Erdos335.BoundaryAvoidingRegularity
import Erdos335.CircleCellPolynomials

/-!
# Character tests on arbitrary finite samples of an additive group
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical ComplexConjugate

namespace Erdos335.IntermediateScale

variable {X G : Type*} [AddCommGroup G]

def pulledCharacterTests (φ : X → G) : Set (X → ℝ) :=
  Set.range fun p : AddChar G Circle × Bool => fun x => circleCoordinate p.2 (p.1 (φ x))

theorem circleCoordinate_bound (b : Bool) (z : Circle) : |circleCoordinate b z| ≤ 1 := by
  cases b
  · exact (Complex.abs_im_le_norm _).trans_eq (Circle.norm_coe z)
  · exact (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe z)

theorem pulledCharacterTests_bound (φ : X → G) (u : X → ℝ)
    (hu : u ∈ pulledCharacterTests φ) (x : X) : |u x| ≤ 1 := by
  obtain ⟨⟨χ, b⟩, rfl⟩ := hu
  exact circleCoordinate_bound b (χ (φ x))

theorem selected_character_factor (φ : X → G) (N M : ℕ) (S : Finset (X → ℝ))
    (hS : ∀ v ∈ S, ∃ u ∈ pulledCharacterTests φ,
      ∃ j : Fin M, v = fun x => shiftedTest N M j (u x)) :
    ∃ (χ : S → AddChar G Circle) (tags : S → Bool × Fin M),
      ∀ v : S, ∀ x, v.val x =
        shiftedTest N M (tags v).2 (circleCoordinate (tags v).1 (χ v (φ x))) := by
  have hw (v : S) : ∃ (χ : AddChar G Circle) (b : Bool) (j : Fin M),
      v.val = fun x => shiftedTest N M j (circleCoordinate b (χ (φ x))) := by
    obtain ⟨u, ⟨⟨χ, b⟩, rfl⟩, j, h⟩ := hS v.val v.property
    exact ⟨χ, b, j, h⟩
  choose χ b j h using hw
  exact ⟨χ, fun v => (b v, j v), fun v x => congrFun (h v) x⟩

theorem pulled_character_sum_norm_le [Fintype X] (φ : X → G) (f : X → ℝ)
    (χ : AddChar G Circle) (ε : ℝ)
    (h : ∀ u ∈ pulledCharacterTests φ,
      |∑ x : X, f x * u x| ≤ ε * Fintype.card X) :
    ‖∑ x : X, (f x : ℂ) * conj (χ (φ x) : ℂ)‖ ≤ 2 * ε * Fintype.card X := by
  have hre := h (fun x => (χ (φ x) : ℂ).re) ⟨(χ, true), rfl⟩
  have him := h (fun x => (χ (φ x) : ℂ).im) ⟨(χ, false), rfl⟩
  have heq : (∑ x : X, (f x : ℂ) * conj (χ (φ x) : ℂ)) =
      ((∑ x : X, f x * (χ (φ x) : ℂ).re : ℝ) : ℂ) -
        Complex.I * ((∑ x : X, f x * (χ (φ x) : ℂ).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [heq]
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (((∑ x : X, f x * (χ (φ x) : ℂ).re : ℝ) : ℂ) -
      Complex.I * ((∑ x : X, f x * (χ (φ x) : ℂ).im : ℝ) : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im, one_mul,
    sub_zero, Complex.sub_im, Complex.mul_im, zero_add, zero_sub, zero_mul, abs_neg] at hnorm
  linarith

end Erdos335.IntermediateScale
