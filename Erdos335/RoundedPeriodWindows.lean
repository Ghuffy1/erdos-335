import Erdos335.DivisiblePhasePeriods

/-!
# Short intervals containing a prescribed divisible approximate period
-/

set_option autoImplicit false

namespace Erdos335.IntermediateScale

theorem ceiling_division_bounds (M W : ℕ) (hM : 0 < M) (hW : 0 < W) :
    let a := (W + M - 1) / M
    0 < a ∧ a ≤ W ∧ W ≤ M * a ∧ M * a < W + M := by
  dsimp only
  let a := (W + M - 1) / M
  have hdiv := Nat.div_add_mod (W + M - 1) M
  have hmod := Nat.mod_lt (W + M - 1) hM
  have hmul : M * a ≤ W + M - 1 := by
    dsimp [a]
    exact Nat.mul_div_le _ _
  have hlo : W ≤ M * a := by change M * a + _ = _ at hdiv; omega
  have hhi : M * a < W + M := by omega
  have ha : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.mul_zero] at hlo
    exact (not_le_of_gt hW) hlo
  have haW : a ≤ W := by
    have hMW : W ≤ M * W := by nlinarith
    have hlt : W + M - 1 < (W + 1) * M := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm W M]
      omega
    have h := (Nat.div_lt_iff_lt_mul hM).mpr hlt
    change a < W + 1 at h
    omega
  exact ⟨ha, haW, hlo, hhi⟩

theorem exists_short_divisible_window (M W : ℕ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hlarge : 8 * (M : ℝ) / ε ≤ W) :
    ∃ a L : ℕ, 0 < a ∧ a ≤ W ∧ W ≤ M * a ∧ a + L ≤ 2 * a ∧
      (ε / 8) * a ≤ L ∧ ((M * (a + L) : ℕ) : ℝ) ≤ (1 + ε) * W := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hWr : (0 : ℝ) < W := (div_pos (by positivity) hε).trans_le hlarge
  have hW : 0 < W := by exact_mod_cast hWr
  let a := (W + M - 1) / M
  obtain ⟨ha, haW, hWa, hMa⟩ := ceiling_division_bounds M W hM hW
  change 0 < a at ha
  change a ≤ W at haW
  change W ≤ M * a at hWa
  change M * a < W + M at hMa
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hWar : (W : ℝ) ≤ (M : ℝ) * a := by exact_mod_cast hWa
  have hMar : (M : ℝ) * a < (W : ℝ) + M := by exact_mod_cast hMa
  have hscale : 8 * (M : ℝ) ≤ ε * W := by
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith
  have haeps : 8 ≤ ε * a := by
    have h := mul_le_mul_of_nonneg_left hWar hε.le
    nlinarith
  let L := ⌊ε * (a : ℝ) / 4⌋₊
  have hfloor : (L : ℝ) ≤ ε * a / 4 := Nat.floor_le (by positivity)
  have hfloor' : ε * a / 4 < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLa : L ≤ a := by
    have h : (L : ℝ) ≤ a := by nlinarith [mul_nonneg (sub_nonneg.mpr hε1) har.le]
    exact_mod_cast h
  have hLlower : (ε / 8) * a ≤ L := by nlinarith
  have hMsmall : (M : ℝ) ≤ ε * W / 8 := by nlinarith
  have htop : ((M * (a + L) : ℕ) : ℝ) ≤ (1 + ε) * W := by
    push_cast
    have hLscaled := mul_le_mul_of_nonneg_left hfloor hMr.le
    have hMaScaled := mul_le_mul_of_nonneg_left hMar.le (show 0 ≤ 1 + ε / 4 by positivity)
    have hMscaled := mul_le_mul_of_nonneg_left hMsmall (show 0 ≤ 1 + ε / 4 by positivity)
    have hepssq : ε ^ 2 * W ≤ ε * W := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hε1) (mul_nonneg hε.le hWr.le)]
    nlinarith
  exact ⟨a, L, ha, haW, hWa, by omega, hLlower, htop⟩

theorem exists_short_divisible_phase_period_constant {I : Type*} [Fintype I]
    (M : ℕ) (hM : 0 < M) (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ ∀ (α : I → ℝ) (W : ℕ), 8 * (M : ℝ) / ε ≤ W →
      (∀ w : I → ℤ, (∀ i, |w i| ≤ (K : ℤ)) →
        circleFrequencyDistance (∑ i, (w i : ℝ) * α i) ≤ 1 / ((K : ℝ) * W) ∨
        (K : ℝ) / W ≤ circleFrequencyDistance (∑ i, (w i : ℝ) * α i)) →
      ∃ Q : ℕ, M ∣ Q ∧ W ≤ Q ∧ (Q : ℝ) < (1 + ε) * W ∧
        ∀ i, ‖unitCharacter ((Q : ℝ) * α i) - 1‖ < η := by
  obtain ⟨K, hK, hperiod⟩ := exists_divisible_phase_period_constant (I := I)
    M hM η (ε / 8) hη (by positivity)
  refine ⟨K, hK, ?_⟩
  intro α W hlarge hgap
  obtain ⟨a, L, ha, haW, hWa, hLa, hLlow, htop⟩ :=
    exists_short_divisible_window M W hM ε hε hε1 hlarge
  obtain ⟨Q, hMQ, hWQ, hQtop, hphase⟩ := hperiod α a L W ha haW hWa hLa hLlow hgap
  have hQtopr : (Q : ℝ) < ((M * (a + L) : ℕ) : ℝ) := by exact_mod_cast hQtop
  exact ⟨Q, hMQ, hWQ, hQtopr.trans_le htop, hphase⟩

end Erdos335.IntermediateScale
