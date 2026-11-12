import Erdos335.PositiveOrbitMeans
import Erdos335.PositivePhasePolynomial
import Erdos335.TorusIntegerOrbit

/-!
# A simultaneous phase hit from a positive Fourier polynomial
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem polynomial_orbit_mean {I : Type*} [Fintype I]
    (S : Finset (I → ℤ)) (q : (I → ℤ) → ℝ) (α : I → ℝ) (a L : ℕ) :
    (∑ m ∈ range L, ∑ w ∈ S, (q w : ℂ) *
      UnitAddTorus.mFourier w (integerTorusOrbit α (a + m))) / (L : ℂ) =
    ∑ w ∈ S, (q w : ℂ) * intervalCharacterMean (∑ i, (w i : ℝ) * α i) a L := by
  simp only [mFourier_integerTorusOrbit]
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro w hw
  dsimp only [intervalCharacterMean]
  rw [← mul_sum, mul_div_assoc]

theorem positive_polynomial_orbit_mean_lower {I : Type*} [Fintype I]
    (S : Finset (I → ℤ)) (q : (I → ℤ) → ℝ) (hq : ∀ w ∈ S, 0 ≤ q w)
    (hzero : (0 : I → ℤ) ∈ S) (α : I → ℝ) (a L : ℕ) (hL : 0 < L)
    (δ κ : ℝ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hdichotomy : ∀ w ∈ S, circleFrequencyDistance (∑ i, (w i : ℝ) * α i) ≤ δ ∨
      κ ≤ ‖unitCharacter (∑ i, (w i : ℝ) * α i) - 1‖) :
    q 0 - (∑ w ∈ S, q w) *
      ((((a + L : ℕ) : ℝ) * (2 * Real.pi * δ)) + 2 / ((L : ℝ) * κ)) ≤
    ((∑ m ∈ range L, ∑ w ∈ S, (q w : ℂ) *
      UnitAddTorus.mFourier w (integerTorusOrbit α (a + m))) / (L : ℂ)).re := by
  classical
  rw [polynomial_orbit_mean]
  let i₀ : ↥S := ⟨0, hzero⟩
  let z : ↥S → ℂ := fun w => intervalCharacterMean (∑ i, (w.val i : ℝ) * α i) a L
  have hz0 : z i₀ = 1 := by
    simp [z, i₀, intervalCharacterMean, unitCharacter, hL.ne']
  have he := positive_weighted_real_sum_lower (fun w : ↥S => q w.val) z i₀
    ((((a + L : ℕ) : ℝ) * (2 * Real.pi * δ)) + 2 / ((L : ℝ) * κ))
    (fun w => hq w.val w.property) (by positivity) hz0
    (fun w hw => intervalCharacterMean_real_lower _ a L hL δ κ hδ hκ
      (hdichotomy w.val w.property))
  have hreal : (∑ w : ↥S, q w.val) = ∑ w ∈ S, q w := by
    exact Finset.sum_attach S q
  have hcomplex : (∑ w : ↥S, (q w.val : ℂ) * z w) =
      ∑ w ∈ S, (q w : ℂ) * intervalCharacterMean (∑ i, (w i : ℝ) * α i) a L := by
    exact Finset.sum_attach S (fun w => (q w : ℂ) *
      intervalCharacterMean (∑ i, (w i : ℝ) * α i) a L)
  simpa only [i₀, hreal, hcomplex] using he

theorem positive_polynomial_phase_hit {I : Type*} [Fintype I]
    (η : ℝ) (S : Finset (I → ℤ)) (q : (I → ℤ) → ℝ)
    (hq : ∀ w ∈ S, 0 ≤ q w) (hzero : (0 : I → ℤ) ∈ S) (hq0 : 0 < q 0)
    (hlocal : ∀ x : UnitAddTorus I, (∃ i, η ≤ ‖fourier (1 : ℤ) (x i) - 1‖) →
      ‖∑ w ∈ S, (q w : ℂ) * UnitAddTorus.mFourier w x‖ ≤ q 0 / 4)
    (α : I → ℝ) (a L : ℕ) (hL : 0 < L) (δ κ : ℝ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hdichotomy : ∀ w ∈ S, circleFrequencyDistance (∑ i, (w i : ℝ) * α i) ≤ δ ∨
      κ ≤ ‖unitCharacter (∑ i, (w i : ℝ) * α i) - 1‖)
    (hbudget : (∑ w ∈ S, q w) *
      ((((a + L : ℕ) : ℝ) * (2 * Real.pi * δ)) + 2 / ((L : ℝ) * κ)) < q 0 / 2) :
    ∃ m < L, ∀ i, ‖unitCharacter (((a + m : ℕ) : ℝ) * α i) - 1‖ < η := by
  classical
  by_contra! hno
  let P : ℕ → ℂ := fun m => ∑ w ∈ S, (q w : ℂ) *
    UnitAddTorus.mFourier w (integerTorusOrbit α (a + m))
  have hbound (m : ℕ) (hm : m < L) : ‖P m‖ ≤ q 0 / 4 := by
    apply hlocal
    obtain ⟨i, hi⟩ := hno m hm
    exact ⟨i, by simpa only [fourier_integerTorusOrbit] using hi⟩
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have havg : ‖(∑ m ∈ range L, P m) / (L : ℂ)‖ ≤ q 0 / 4 := by
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hLR).mpr
    calc
      _ ≤ ∑ m ∈ range L, ‖P m‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ range L, q 0 / 4 := sum_le_sum fun m hm => hbound m (mem_range.mp hm)
      _ = _ := by simp; ring
  have hlower := positive_polynomial_orbit_mean_lower S q hq hzero α a L hL δ κ hδ hκ hdichotomy
  change q 0 - _ ≤ ((∑ m ∈ range L, P m) / (L : ℂ)).re at hlower
  have hre := Complex.re_le_norm ((∑ m ∈ range L, P m) / (L : ℂ))
  linarith

end Erdos335.IntermediateScale
