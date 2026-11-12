import Erdos335.FiniteCharacterFrequencies
import Erdos335.UniformConvolutionBound
import Erdos335.WindowFourierNorm

/-!
# Fourier coefficients of a window embedded in a finite cyclic group
-/

set_option autoImplicit false

open Finset
open scoped BigOperators ComplexConjugate

namespace Erdos335.IntermediateScale

theorem sum_zmod_eq_range {M : ℕ} [NeZero M] (f : ZMod M → ℂ) :
    (∑ x : ZMod M, f x) = ∑ i ∈ range M, f (i : ZMod M) := by
  have he (i : Fin M) : (ZMod.finEquiv M) i = (i.val : ZMod M) := by
    have hv : ((ZMod.finEquiv M) i).val = i.val := by
      cases M with
      | zero => exact Fin.elim0 i
      | succ M => rfl
    simpa only [hv] using (ZMod.natCast_zmod_val ((ZMod.finEquiv M) i)).symm
  rw [Finset.sum_range]
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv M).toEquiv
  intro i
  exact congrArg f (he i).symm

noncomputable def cyclicFourierWindow (r : ℕ → ℝ) (n W M : ℕ) (x : ZMod M) : ℂ :=
  if x.val < W then (r (n + x.val) : ℂ) else 0

theorem cyclicFourierWindow_coefficient_le (r : ℕ → ℝ) (n W M : ℕ) [NeZero M]
    (hW : 0 < W) (hWM : W ≤ M) (χ : AddChar (ZMod M) ℂ) :
    ‖Erdos335.FiniteFourier.coefficient (cyclicFourierWindow r n W M) χ‖ ≤ windowFourierNorm r n W := by
  obtain ⟨β, hβ⟩ := finite_character_integer_frequency χ (Int.castAddHom (ZMod M))
  have hchar (i : ℕ) : conj (χ (i : ZMod M)) = unitCharacter ((i : ℝ) * β) := by
    simpa using hβ (i : ℤ)
  have hfilter : (range M).filter (fun i => i < W) = range W := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  have hsum : (∑ x : ZMod M, cyclicFourierWindow r n W M x * conj (χ x)) =
      ∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β) := by
    rw [sum_zmod_eq_range]
    calc
      _ = ∑ i ∈ range M, if i < W then (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β) else 0 := by
        apply sum_congr rfl
        intro i hi
        rw [cyclicFourierWindow, ZMod.val_cast_of_lt (mem_range.mp hi)]
        by_cases h : i < W <;> simp only [h, ite_true, ite_false, zero_mul, hchar]
      _ = ∑ i ∈ (range M).filter (fun i => i < W), (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β) := by
        rw [sum_filter]
      _ = _ := by rw [hfilter]
  have hcoeff : Erdos335.FiniteFourier.coefficient (cyclicFourierWindow r n W M) χ =
      (∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)) / (M : ℂ) := by
    rw [Erdos335.FiniteFourier.coefficient_eq_expect, Fintype.expect_eq_sum_div_card, hsum, ZMod.card]
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hMr : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hsup := le_ciSup (window_fourier_coefficients_bddAbove r n W) β
  rw [norm_div, Complex.norm_natCast] at hsup
  have hnum := (div_le_iff₀ hWr).mp hsup
  rw [hcoeff, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hMr).mpr
  exact hnum.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hWM)
    (windowFourierNorm_nonneg r n W))

theorem cyclicFourierWindow_convolution_l1_le (r : ℕ → ℝ) (n W M : ℕ) [NeZero M]
    (hW : 0 < W) (hWM : W ≤ M) (g : ZMod M → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) :
    (∑ x : ZMod M, ‖Erdos335.FiniteFourier.convolution (cyclicFourierWindow r n W M) g x‖) / M ≤
      windowFourierNorm r n W := by
  simpa only [ZMod.card] using Erdos335.FiniteFourier.convolution_l1_le_of_coefficients
    (cyclicFourierWindow r n W M) g (windowFourierNorm r n W) (windowFourierNorm_nonneg r n W)
    (fun χ => cyclicFourierWindow_coefficient_le r n W M hW hWM χ) hg

end Erdos335.IntermediateScale
