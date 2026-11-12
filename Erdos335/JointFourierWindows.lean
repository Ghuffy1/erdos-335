import Erdos335.IntermediateFourierModel
import Erdos335.JointConvolutionWindows
import Erdos335.IntermediateConvolutionPeriods

/-!
# Common-start windows from finitely many Fourier models
-/

set_option autoImplicit false

open Filter Set Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_joint_fourier_convolution_windows {I : Type*} [Fintype I]
    (A B : I → Set ℕ) (N L U : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (hLpos : ∀ s, 0 < L s) (hUpos : ∀ s, 0 < U s) (hL : Tendsto L atTop atTop)
    (hLU : Tendsto (fun s => (L s : ℝ) / U s) atTop (𝓝 0))
    (hUN : Tendsto (fun s => (U s : ℝ) / N s) atTop (𝓝 0))
    (m : ∀ i, IntermediateFourierModel ((A i).indicator (fun _ => (1 : ℝ))) N L U) :
    ∃ (H start : ℕ → ℕ) (q : I → ℕ → ℕ+),
      (∀ s, 0 < H s) ∧ Tendsto H atTop atTop ∧
      Tendsto (fun s => (L s : ℝ) / H s) atTop (𝓝 0) ∧
      Tendsto (fun s => (H s : ℝ) / U s) atTop (𝓝 0) ∧
      Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0) ∧
      (∀ s, 0 < start s) ∧ ∀ i,
        (∀ s, H s ≤ (q i s : ℕ)) ∧ Tendsto (fun s => (q i s : ℕ)) atTop atTop ∧
        Tendsto (fun s => (((q i s : ℕ) - H s : ℕ) : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
        (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q i s : ℕ)) ∧
        (∀ᶠ s in atTop, start s + (q i s : ℕ) ≤ N s) ∧
        Tendsto (fun s => convolutionTranslationError (A i) (B i) (start s) (q i s : ℕ) /
          ((q i s : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  classical
  let H := positiveIntermediateScale L U (1 / 2) 0
  have hHpos : ∀ s, 0 < H s := positiveIntermediateScale_pos L U _ _
  have hUtop := scale_tendsto_atTop_of_smaller L U hL hUpos hLU
  have hUL := reciprocal_scale_ratio_tendsto_atTop L U hLpos hUpos hLU
  have hHtop : Tendsto H atTop atTop :=
    positiveIntermediateScale_atTop L U hL hUL _ _ (by norm_num)
  have hLH : Tendsto (fun s => (L s : ℝ) / H s) atTop (𝓝 0) :=
    positiveIntermediateScale_lower_ratio L U hL hUL _ _ (by norm_num)
  have hHU : Tendsto (fun s => (H s : ℝ) / U s) atTop (𝓝 0) :=
    positiveIntermediateScale_ambient_ratio L U U hL hUtop hUL
      (Eventually.of_forall fun _ => le_rfl) _ _ (by norm_num) (by norm_num)
  have hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0) :=
    window_ratio_tendsto_zero_of_intermediate N U H hUpos hHU hUN
  have hF (i : I) (n : ℕ) : (A i).indicator (fun _ => (1 : ℝ)) n ∈ Icc (0 : ℝ) 1 := by
    by_cases hn : n ∈ A i <;> simp [hn]
  have hperiods (i : I) := (intermediate_fourier_convolution_and_periods 6 (by decide)
    ((A i).indicator (fun _ => (1 : ℝ))) (m i).structured (hF i) (m i).bounded
    (m i).dimension (m i).coefficient (m i).frequency (m i).coefficient_bound
    N L U hN (m i).approximation
    (fun W hW hLW hWU => (m i).control W (Eventually.of_forall hW) hLW hWU)
    H hHpos hHtop hLH hHU hHN).2
  choose Q ε hεpos hεlim hQ hdiv hperiod using hperiods
  have hL6H : Tendsto (fun s => (L s : ℝ) / (6 * H s : ℕ)) atTop (𝓝 0) := by
    have heq : (fun s => (L s : ℝ) / (6 * H s : ℕ)) = fun s => ((L s : ℝ) / H s) / 6 := by
      funext s
      push_cast
      ring
    rw [heq]
    simpa only [zero_div] using hLH.div_const 6
  have h6HU : Tendsto (fun s => ((6 * H s : ℕ) : ℝ) / U s) atTop (𝓝 0) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, mul_zero] using hHU.const_mul 6
  have hFourier (i : I) := ((m i).control (fun s => 6 * H s)
    (Eventually.of_forall fun s => Nat.mul_pos (by decide) (hHpos s)) hL6H h6HU).1
  obtain ⟨start, q, hstart, hq⟩ := exists_joint_convolution_windows A B (fun i => (m i).structured)
    N H hN hHpos hHtop hHN Q ε (fun i s => (hεpos i s).le) hεlim hQ hdiv hFourier hperiod
  exact ⟨H, start, q, hHpos, hHtop, hLH, hHU, hHN, hstart, hq⟩

end Erdos335.IntermediateScale
