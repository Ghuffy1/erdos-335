import Erdos335.PositivePolynomialOrbit

/-!
# Simultaneous approximate periods from a frequency gap

The proof uses a localized polynomial with nonnegative Fourier coefficients.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem phase_orbit_error_bound (a L H : ℕ) (C ρ : ℝ)
    (hH : 0 < H) (hC : 0 < C) (hρ : 0 < ρ)
    (hupper : a + L ≤ 2 * H) (hlower : ρ * H ≤ L) :
    (((a + L : ℕ) : ℝ) * (2 * Real.pi * (1 / (C * H)))) +
      2 / ((L : ℝ) * (4 * C / H)) ≤ (4 * Real.pi + 1 / (2 * ρ)) / C := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hu : ((a + L : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hupper
  have hL : (0 : ℝ) < L := (mul_pos hρ hHr).trans_le hlower
  have hfirst : ((a + L : ℕ) : ℝ) * (2 * Real.pi * (1 / (C * H))) ≤ 4 * Real.pi / C := by
    calc
      _ ≤ (2 * H) * (2 * Real.pi * (1 / (C * H))) :=
        mul_le_mul_of_nonneg_right hu (by positivity)
      _ = _ := by field_simp; ring
  have hden : 4 * ρ * C ≤ (L : ℝ) * (4 * C / H) := by
    calc
      _ = (ρ * H) * (4 * C / H) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hlower (by positivity)
  have hsecond : 2 / ((L : ℝ) * (4 * C / H)) ≤ (1 / (2 * ρ)) / C := by
    calc
      _ ≤ 2 / (4 * ρ * C) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = _ := by ring
  calc
    _ ≤ 4 * Real.pi / C + (1 / (2 * ρ)) / C := add_le_add hfirst hsecond
    _ = _ := by ring

theorem exists_simultaneous_approximate_period_constant {I : Type*} [Fintype I]
    (η ρ : ℝ) (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (α : I → ℝ) (a L H : ℕ),
      0 < H → a + L ≤ 2 * H → ρ * H ≤ L →
      (∀ w : I → ℤ, (∀ i, |w i| ≤ (C : ℤ)) →
        circleFrequencyDistance (∑ i, (w i : ℝ) * α i) ≤ 1 / ((C : ℝ) * H) ∨
        (C : ℝ) / H ≤ circleFrequencyDistance (∑ i, (w i : ℝ) * α i)) →
      ∃ m < L, ∀ i, ‖unitCharacter (((a + m : ℕ) : ℝ) * α i) - 1‖ < η := by
  classical
  obtain ⟨S, q, hzero, hq, hq0, hlocal⟩ := exists_positive_phase_polynomial (I := I) η hη
  let mass : ℝ := ∑ w ∈ S, q w
  have hmass : 0 ≤ mass := sum_nonneg fun w hw => hq w
  let D : ℝ := 4 * Real.pi + 1 / (2 * ρ)
  have hD : 0 < D := by dsimp [D]; positivity
  let W : ℕ := ∑ w ∈ S, ∑ i, (w i).natAbs
  obtain ⟨C, hC⟩ := exists_nat_gt (max (W : ℝ) (2 * mass * D / q 0 + 1))
  have hWC : (W : ℝ) < C := (le_max_left _ _).trans_lt hC
  have hbudgetC : 2 * mass * D / q 0 + 1 < C := (le_max_right _ _).trans_lt hC
  have hCr : (0 : ℝ) < C := by
    have ht : 0 ≤ 2 * mass * D / q 0 := by positivity
    linarith
  have hCn : 0 < C := by exact_mod_cast hCr
  have hweight (w : I → ℤ) (hw : w ∈ S) (i : I) : |w i| ≤ (C : ℤ) := by
    have hwi : (w i).natAbs ≤ W :=
      (single_le_sum (fun j hj => Nat.zero_le (w j).natAbs) (mem_univ i)).trans
        (single_le_sum (fun v hv => Nat.zero_le (∑ j, (v j).natAbs)) hw)
    have hWCnat : W ≤ C := by exact_mod_cast hWC.le
    have hint : ((w i).natAbs : ℤ) ≤ (C : ℤ) := by exact_mod_cast hwi.trans hWCnat
    simpa only [Int.natCast_natAbs] using hint
  refine ⟨C, hCn, ?_⟩
  intro α a L H hH hupper hlower hgap
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hLr : (0 : ℝ) < L := (mul_pos hρ hHr).trans_le hlower
  have hL : 0 < L := by exact_mod_cast hLr
  have hκ : 0 < 4 * (C : ℝ) / H := by positivity
  have hdichotomy (w : I → ℤ) (hw : w ∈ S) :
      circleFrequencyDistance (∑ i, (w i : ℝ) * α i) ≤ 1 / ((C : ℝ) * H) ∨
      4 * (C : ℝ) / H ≤ ‖unitCharacter (∑ i, (w i : ℝ) * α i) - 1‖ := by
    rcases hgap w (hweight w hw) with hs | hl
    · exact Or.inl hs
    · right
      have hb := (unitCharacter_distance_bounds (∑ i, (w i : ℝ) * α i)).1
      have ht := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 4)
      calc
        _ = 4 * ((C : ℝ) / H) := by ring
        _ ≤ _ := ht.trans hb
  have herror := phase_orbit_error_bound a L H C ρ hH hCr hρ hupper hlower
  have hbudget : mass *
      ((((a + L : ℕ) : ℝ) * (2 * Real.pi * (1 / ((C : ℝ) * H)))) +
        2 / ((L : ℝ) * (4 * (C : ℝ) / H))) < q 0 / 2 := by
    have hc : 2 * mass * D < (C : ℝ) * q 0 :=
      (div_lt_iff₀ hq0).mp (by linarith)
    calc
      _ ≤ mass * (D / C) := mul_le_mul_of_nonneg_left herror hmass
      _ = (mass * D) / C := by ring
      _ < q 0 / 2 := (div_lt_iff₀ hCr).mpr (by nlinarith)
  exact positive_polynomial_phase_hit η S q (fun w hw => hq w) hzero hq0
    (fun x hx => (hlocal x hx).le) α a L hL (1 / ((C : ℝ) * H)) (4 * (C : ℝ) / H)
    (by positivity) hκ hdichotomy hbudget

end Erdos335.IntermediateScale
