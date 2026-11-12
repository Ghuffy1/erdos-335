import Erdos335.CompactCircleEquiv
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Circular distance expressed by the principal argument
-/

set_option autoImplicit false

namespace Erdos335.Loeb

theorem norm_unitAddCircle_eq_arg (x : AddCircle (1 : ℝ)) :
    ‖x‖ = |Complex.arg (AddCircle.toCircle x : ℂ)| / (2 * Real.pi) := by
  let a : ℝ := Complex.arg (AddCircle.toCircle x : ℂ) / (2 * Real.pi)
  have ha : (a : AddCircle (1 : ℝ)) = x := by
    apply AddCircle.injective_toCircle one_ne_zero
    rw [AddCircle.toCircle_apply_mk]
    have hscale : 2 * Real.pi / 1 * a = Complex.arg (AddCircle.toCircle x : ℂ) := by
      dsimp [a]
      field_simp
    rw [hscale]
    exact Circle.exp_arg _
  have habound : |a| ≤ |(1 : ℝ)| / 2 := by
    dsimp [a]
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    have harg := Complex.abs_arg_le_pi (AddCircle.toCircle x : ℂ)
    rw [div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    norm_num only [abs_one] at *
    nlinarith
  calc
    ‖x‖ = ‖(a : AddCircle (1 : ℝ))‖ := congrArg norm ha.symm
    _ = |a| := (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr habound
    _ = _ := by
      dsimp [a]
      rw [abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]

end Erdos335.Loeb
