import Erdos335.SimultaneousApproximatePeriod

/-!
# Simultaneous approximate periods divisible by a prescribed integer
-/

set_option autoImplicit false

open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem frequency_gap_after_integer_dilation {I : Type*} [Fintype I]
    (α : I → ℝ) (M C W a : ℕ) (hM : 0 < M) (hC : 0 < C)
    (ha : 0 < a) (haW : a ≤ W) (hWMa : W ≤ M * a)
    (hgap : ∀ u : I → ℤ, (∀ i, |u i| ≤ ((M * C : ℕ) : ℤ)) →
      circleFrequencyDistance (∑ i, (u i : ℝ) * α i) ≤ 1 / (((M * C : ℕ) : ℝ) * W) ∨
      ((M * C : ℕ) : ℝ) / W ≤ circleFrequencyDistance (∑ i, (u i : ℝ) * α i))
    (w : I → ℤ) (hw : ∀ i, |w i| ≤ (C : ℤ)) :
    circleFrequencyDistance (∑ i, (w i : ℝ) * ((M : ℝ) * α i)) ≤ 1 / ((C : ℝ) * a) ∨
      (C : ℝ) / a ≤ circleFrequencyDistance (∑ i, (w i : ℝ) * ((M : ℝ) * α i)) := by
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hWr : (0 : ℝ) < W := har.trans_le (by exact_mod_cast haW)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hweight (i : I) : |(M : ℤ) * w i| ≤ ((M * C : ℕ) : ℤ) := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg M), Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (hw i) (Int.natCast_nonneg M)
  have hsum : (∑ i, (((M : ℤ) * w i : ℤ) : ℝ) * α i) =
      ∑ i, (w i : ℝ) * ((M : ℝ) * α i) := by
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  have hKC : C ≤ M * C := by nlinarith
  have hlow : 1 / (((M * C : ℕ) : ℝ) * W) ≤ 1 / ((C : ℝ) * a) := by
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hCr har)
    exact mul_le_mul (by exact_mod_cast hKC) (by exact_mod_cast haW) har.le
      (by positivity)
  have hhigh : (C : ℝ) / a ≤ ((M * C : ℕ) : ℝ) / W := by
    apply (div_le_div_iff₀ har hWr).mpr
    have ht := mul_le_mul_of_nonneg_left (show (W : ℝ) ≤ M * a by exact_mod_cast hWMa) hCr.le
    push_cast
    nlinarith
  rcases hgap (fun i => (M : ℤ) * w i) hweight with hs | hl
  · rw [hsum] at hs
    exact Or.inl (hs.trans hlow)
  · rw [hsum] at hl
    exact Or.inr (hhigh.trans hl)

theorem exists_divisible_phase_period_constant {I : Type*} [Fintype I]
    (M : ℕ) (hM : 0 < M) (η ρ : ℝ) (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ K : ℕ, 0 < K ∧ ∀ (α : I → ℝ) (a L W : ℕ),
      0 < a → a ≤ W → W ≤ M * a → a + L ≤ 2 * a → ρ * a ≤ L →
      (∀ w : I → ℤ, (∀ i, |w i| ≤ (K : ℤ)) →
        circleFrequencyDistance (∑ i, (w i : ℝ) * α i) ≤ 1 / ((K : ℝ) * W) ∨
        (K : ℝ) / W ≤ circleFrequencyDistance (∑ i, (w i : ℝ) * α i)) →
      ∃ Q : ℕ, M ∣ Q ∧ W ≤ Q ∧ Q < M * (a + L) ∧
        ∀ i, ‖unitCharacter ((Q : ℝ) * α i) - 1‖ < η := by
  obtain ⟨C, hC, hperiod⟩ := exists_simultaneous_approximate_period_constant (I := I) η ρ hη hρ
  refine ⟨M * C, Nat.mul_pos hM hC, ?_⟩
  intro α a L W ha haW hWMa hupper hlower hgap
  obtain ⟨m, hm, hphase⟩ := hperiod (fun i => (M : ℝ) * α i) a L a ha hupper hlower
    (frequency_gap_after_integer_dilation α M C W a hM hC ha haW hWMa hgap)
  refine ⟨M * (a + m), dvd_mul_right _ _, ?_, ?_, ?_⟩
  · exact hWMa.trans (Nat.mul_le_mul_left M (Nat.le_add_right a m))
  · exact Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_left hm a) hM
  · intro i
    convert hphase i using 1 <;> push_cast <;> ring

end Erdos335.IntermediateScale
