import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Finite conditional averages for arithmetic regularity

The averages preserve the interval `[0,1]` and give an exactly orthogonal
decomposition. These are the finite energy identities used in the
intermediate-scale regularity construction.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

variable {G K : Type*} [Fintype G] [Fintype K] [DecidableEq K]

noncomputable def finiteFiber (π : G → K) (k : K) : Finset G :=
  univ.filter fun x => π x = k

noncomputable def finiteFiberMean (π : G → K) (f : G → ℝ) (k : K) : ℝ :=
  (∑ x ∈ finiteFiber π k, f x) / (finiteFiber π k).card

noncomputable def finiteConditionalMean (π : G → K) (f : G → ℝ) (x : G) : ℝ :=
  finiteFiberMean π f (π x)

omit [Fintype K] in
theorem finiteFiber_residual_sum (π : G → K) (f : G → ℝ) (k : K) :
    ∑ x ∈ finiteFiber π k, (f x - finiteFiberMean π f k) = 0 := by
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  by_cases h : (finiteFiber π k).card = 0
  · have he : finiteFiber π k = ∅ := card_eq_zero.mp h
    simp [he]
  · have hc : ((finiteFiber π k).card : ℝ) ≠ 0 := by exact_mod_cast h
    rw [finiteFiberMean]
    field_simp
    ring

omit [Fintype K] in
theorem finiteConditionalMean_bounds (π : G → K) (f : G → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (x : G) :
    finiteConditionalMean π f x ∈ Set.Icc (0 : ℝ) 1 := by
  have hpos : 0 < (finiteFiber π (π x)).card := card_pos.mpr
    ⟨x, mem_filter.mpr ⟨mem_univ x, rfl⟩⟩
  have hc : (0 : ℝ) < (finiteFiber π (π x)).card := by exact_mod_cast hpos
  constructor
  · exact div_nonneg (sum_nonneg (fun y _ => (hf y).1)) hc.le
  · apply (div_le_iff₀ hc).mpr
    calc
      (∑ y ∈ finiteFiber π (π x), f y) ≤ ∑ _y ∈ finiteFiber π (π x), (1 : ℝ) :=
        sum_le_sum fun y _ => (hf y).2
      _ = _ := by simp

theorem finiteConditionalMean_orthogonal (π : G → K) (f : G → ℝ) (g : K → ℝ) :
    ∑ x : G, g (π x) * (f x - finiteConditionalMean π f x) = 0 := by
  rw [← sum_fiberwise (univ : Finset G) π]
  apply sum_eq_zero
  intro k hk
  calc
    _ = g k * ∑ x ∈ finiteFiber π k, (f x - finiteFiberMean π f k) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      have hπ : π x = k := (mem_filter.mp hx).2
      simp only [finiteConditionalMean, hπ]
    _ = 0 := by rw [finiteFiber_residual_sum, mul_zero]

theorem finiteConditionalMean_sum (π : G → K) (f : G → ℝ) :
    ∑ x : G, finiteConditionalMean π f x = ∑ x : G, f x := by
  have h := finiteConditionalMean_orthogonal π f (fun _ => 1)
  simp only [one_mul, sum_sub_distrib] at h
  linarith

theorem finiteConditionalMean_energy_identity (π : G → K) (f : G → ℝ) :
    ∑ x : G, f x ^ 2 = (∑ x : G, finiteConditionalMean π f x ^ 2) +
      ∑ x : G, (f x - finiteConditionalMean π f x) ^ 2 := by
  have h := finiteConditionalMean_orthogonal π f (finiteFiberMean π f)
  change (∑ x : G, finiteConditionalMean π f x * (f x - finiteConditionalMean π f x)) = 0 at h
  calc
    _ = ∑ x : G, (finiteConditionalMean π f x ^ 2 +
        (f x - finiteConditionalMean π f x) ^ 2 +
        2 * (finiteConditionalMean π f x * (f x - finiteConditionalMean π f x))) := by
      apply sum_congr rfl
      intro x hx
      ring
    _ = _ := by rw [sum_add_distrib, sum_add_distrib, ← mul_sum, h]; ring

theorem finiteConditionalMean_energy_le (π : G → K) (f : G → ℝ) :
    (∑ x : G, finiteConditionalMean π f x ^ 2) ≤ ∑ x : G, f x ^ 2 := by
  rw [finiteConditionalMean_energy_identity π f]
  exact le_add_of_nonneg_right (sum_nonneg fun _ _ => sq_nonneg _)

end Erdos335.IntermediateScale
