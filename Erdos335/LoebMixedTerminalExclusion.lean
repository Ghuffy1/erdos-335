import Erdos335.LoebPhysicalQuasiOff
import Erdos335.LoebPhysicalBohrOutput
import Erdos335.LoebQuasiBohrFiniteProfiles
import Erdos335.MixedResidueProfiles
import Erdos335.LoebQuasiPeriodicSaturation

/-!
# Incompatible positive and null-prefix terminal orientations
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance mixedTerminalLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem no_mixed_positive_null_terminal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q₀ q₁ : ℕ → ℕ+)
    (hdiv₀ : ∀ n : ℕ+, ∀ᶠ s in U, (n : ℕ) ∣ (q₀ s : ℕ))
    (hdiv₁ : ∀ n : ℕ+, ∀ᶠ s in U, (n : ℕ) ∣ (q₁ s : ℕ))
    (P₀ W₀ : Set ((U : Filter ℕ).Product (fun n => ZMod (q₀ n : ℕ))))
    (W₁ P₁ : Set ((U : Filter ℕ).Product (fun n => ZMod (q₁ n : ℕ))))
    (p₀ : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) P₀ W₀)
    (p₁ : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) W₁ P₁)
    (hzero : loebMeasure U hU p₀.left.active = 0)
    (k : ℕ+) (hker₀ : (finiteQuotient U (fun n => naturalCyclicProjection (q₀ n) k)).ker = p₀.period)
    (d : InternalBohrPairData U hU q₁ p₁.left.active p₁.right.active)
    (hperiod₁ : p₁.period = (finiteQuotient U d.residue).ker)
    (hSm₀ : MeasurableSet (P₀ + W₀)) (hSm₁ : MeasurableSet (W₁ + P₁))
    (b : ℝ) (hm₀ : (loebMeasure U hU P₀).toReal = b) (hm₁ : (loebMeasure U hU W₁).toReal = b)
    (C : Set ℕ) (start : ℕ → ℕ)
    (hmodel₀ : P₀ + W₀ =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow C (start n) (q₀ n : ℕ) : Set (ZMod (q₀ n : ℕ)))))
    (hmodel₁ : W₁ + P₁ =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow C (start n) (q₁ n : ℕ) : Set (ZMod (q₁ n : ℕ)))))
    (hagree : ∀ n : ℕ+, ∀ r : ZMod (n : ℕ),
      actualWindowProfile U hU q₀ n C start r = actualWindowProfile U hU q₁ n C start r) : False := by
  classical
  let h := d.modulus
  let N := h * k
  have hhN : (h : ℕ) ∣ (N : ℕ) := ⟨k, rfl⟩
  have hkN : (k : ℕ) ∣ (N : ℕ) := ⟨h, Nat.mul_comm _ _⟩
  let sum₀ := loeb_quasiPeriodic_sum_decomposition U hU q₀ P₀ W₀ p₀ hSm₀
  let u := finiteQuotient U (fun n => naturalCyclicProjection (q₀ n) k) sum₀.anchor +
    finiteValue U (fun n => (start n : ZMod (k : ℕ)))
  let v := finiteQuotient U d.residue (d.left_anchor + d.right_anchor) +
    finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  let R := ((finiteQuotient U d.residue) '' (W₁ + P₁)).toFinite.toFinset
  have hR : (finiteQuotient U d.residue) '' (W₁ + P₁) = (R : Set _) := by ext r; simp [R]
  have hpartial (r : ZMod (N : ℕ)) (hr : naturalCyclicProjection N h r = v) :
      actualWindowProfile U hU q₁ N C start r = d.left_length + d.right_length := by
    have hp := loeb_physical_bohr_output_profile U hU q₁ W₁ P₁ p₁ hSm₁ d hperiod₁ C start hmodel₁
      R hR N (hdiv₁ N) hhN r
    rw [if_pos hr] at hp
    exact hp
  have hoff (r : ZMod (N : ℕ)) (hr : naturalCyclicProjection N k r ≠ u) :
      actualWindowProfile U hU q₁ N C start r = 0 ∨ actualWindowProfile U hU q₁ N C start r = 1 := by
    have hp := loeb_physical_quasi_off_active U hU q₀ (P₀ + W₀) p₀.period sum₀ k hker₀ C start hmodel₀
      N (hdiv₀ N) hkN r hr
    rwa [hagree N r] at hp
  have hkh : (k : ℕ) ∣ (h : ℕ) := modulus_dvd_of_partial_profile N h k hhN hkN v u
    (actualWindowProfile U hU q₁ N C start) (d.left_length + d.right_length)
    (add_pos d.left_positive d.right_positive) d.length_sum_lt_one hpartial hoff
  obtain ⟨M, hM⟩ := loeb_quasiPeriodic_null_mass_integer U hU q₀ P₀ p₀.period p₀.left hzero k (hdiv₀ k) hker₀
  rw [hm₀] at hM
  let X := ((finiteQuotient U d.residue) '' W₁).toFinite.toFinset
  have hX : (finiteQuotient U d.residue) '' W₁ = (X : Set _) := by ext r; simp [X]
  have hmass : b = ((X.card : ℝ) - 1 + d.left_length) / (h : ℕ) :=
    hm₁.symm.trans (loeb_quasiBohr_right_mass U hU q₁ P₁ W₁ p₁.swap d.swap hperiod₁ (hdiv₁ h) X hX)
  have hpartialMass : ((h : ℕ) : ℝ) * b = (((X.card : ℤ) - 1 : ℤ) : ℝ) + d.left_length := by
    rw [hmass]
    push_cast
    field_simp
  exact no_integer_and_partial_mass h k hkh b d.left_length d.left_positive
    (by linarith [d.length_sum_lt_one, d.right_positive]) M ((X.card : ℤ) - 1) hM hpartialMass

end Erdos335.Loeb

end
