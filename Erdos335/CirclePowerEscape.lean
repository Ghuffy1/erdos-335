import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# A quantitatively bounded power outside the right semicircle
-/

set_option autoImplicit false

namespace Erdos335.Loeb

theorem exists_circle_power_nonpositive_real
    (z : Circle) (hne : z ≠ 1) :
    ∃ n : ℕ, 0 < n ∧ (z ^ n : ℂ).re ≤ 0 ∧
      (n : ℝ) * |Complex.arg (z : ℂ)| ≤ Real.pi := by
  let a := |Complex.arg (z : ℂ)|
  have ha : 0 < a := by
    apply abs_pos.mpr
    intro hz
    apply hne
    simpa only [hz, Circle.exp_zero] using (Circle.exp_arg z).symm
  have hapi : a ≤ Real.pi := Complex.abs_arg_le_pi (z : ℂ)
  have hstep : ∃ n : ℕ, 0 < n ∧ Real.pi / 2 ≤ (n : ℝ) * a ∧ (n : ℝ) * a ≤ Real.pi := by
    by_cases hsmall : a ≤ Real.pi / 2
    · let n := Nat.ceil ((Real.pi / 2) / a)
      have hn : 0 < n := Nat.ceil_pos.mpr (div_pos (by positivity) ha)
      have hlower : Real.pi / 2 ≤ (n : ℝ) * a :=
        (div_le_iff₀ ha).mp (Nat.le_ceil ((Real.pi / 2) / a))
      have hupper : (n : ℝ) * a < Real.pi / 2 + a := by
        have hceil := Nat.ceil_lt_add_one (div_nonneg (by positivity : 0 ≤ Real.pi / 2) ha.le)
        have hmul := mul_lt_mul_of_pos_right hceil ha
        simpa only [n, add_mul, div_mul_cancel₀ _ ha.ne', one_mul] using hmul
      exact ⟨n, hn, hlower, by linarith⟩
    · exact ⟨1, Nat.zero_lt_one, by simpa using (not_le.mp hsmall).le, by simpa using hapi⟩
  obtain ⟨n, hn, hlower, hupper⟩ := hstep
  refine ⟨n, hn, ?_, hupper⟩
  have hpower : Circle.exp ((n : ℝ) * Complex.arg (z : ℂ)) = z ^ n := by
    rw [Circle.exp_natCast_mul, Circle.exp_arg]
  have hreal : (z ^ n : ℂ).re = Real.cos ((n : ℝ) * Complex.arg (z : ℂ)) := by
    have heq := congrArg (fun w : Circle => (w : ℂ).re) hpower.symm
    simpa only [Circle.coe_pow, Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using heq
  have habs : |(n : ℝ) * Complex.arg (z : ℂ)| = (n : ℝ) * a := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  rw [hreal, ← Real.cos_abs, habs]
  exact Real.cos_nonpos_of_pi_div_two_le_of_le hlower (by linarith [Real.pi_pos])

end Erdos335.Loeb
