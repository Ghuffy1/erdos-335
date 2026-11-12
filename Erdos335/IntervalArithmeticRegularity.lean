import Erdos335.IntegerSampleRegularity

/-!
# Arithmetic regularity on a finite integer interval

This is the finite regularity statement used in the intermediate-scale proof,
with unit coefficients, real frequencies, a bounded structured part, exact
mean preservation, and exact orthogonality.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

noncomputable def intervalFourierNorm {N : ℕ} (f : Fin N → ℂ) : ℝ :=
  ⨆ α : ℝ, ‖(∑ i : Fin N, f i * unitCharacter (((i.val : ℝ) + 1) * α)) / (N : ℂ)‖

theorem intervalFourierNorm_le {N : ℕ} (hN : 0 < N) (f : Fin N → ℂ) (ε : ℝ)
    (h : ∀ α : ℝ, ‖∑ i : Fin N, f i * unitCharacter (((i.val : ℝ) + 1) * α)‖ ≤ ε * N) :
    intervalFourierNorm f ≤ ε := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply ciSup_le
  intro α
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ hNr).mpr (h α)

theorem interval_arithmetic_regularity (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ (N : ℕ), 0 < N → ∀ f : Fin N → ℝ,
      (∀ i, f i ∈ Set.Icc (0 : ℝ) 1) →
      ∃ (s r : Fin N → ℝ) (α : Fin L → ℝ) (a : Fin L → ℂ),
        (∀ i, f i = s i + r i) ∧
        (∀ i, s i ∈ Set.Icc (0 : ℝ) 1 ∧ r i ∈ Set.Icc (-1 : ℝ) 1) ∧
        (∑ i : Fin N, r i) = 0 ∧
        (∑ i : Fin N, s i * r i) = 0 ∧
        (∀ j, ‖a j‖ ≤ 1) ∧
        intervalFourierNorm (fun i => (r i : ℂ)) ≤ ε ∧
        (∑ i : Fin N, ‖(s i : ℂ) -
          ∑ j, a j * unitCharacter (((i.val : ℝ) + 1) * α j)‖ ^ 2) / N ≤ ε ^ 2 := by
  obtain ⟨L, hL, hreg⟩ := integer_sample_regularity.{0} ε hε
  refine ⟨L, hL, ?_⟩
  intro N hN f hf
  let : NeZero N := ⟨hN.ne'⟩
  let φ : Fin N → ℤ := fun i => (i.val : ℤ) + 1
  obtain ⟨s, α, a, hs, hsum, horth, ha, htest, happrox⟩ := hreg (Fin N) φ f hf
  let r := fun i => f i - s i
  have hφ (i : Fin N) : (φ i : ℝ) = (i.val : ℝ) + 1 := by simp [φ]
  refine ⟨s, r, α, a, fun i => by dsimp [r]; ring, ?_, ?_, horth, ha, ?_, ?_⟩
  · intro i
    refine ⟨hs i, ?_⟩
    have hsi := hs i
    have hfi := hf i
    constructor <;> dsimp [r] <;> linarith [hsi.1, hsi.2, hfi.1, hfi.2]
  · dsimp [r]
    rw [sum_sub_distrib, hsum, sub_self]
  · apply intervalFourierNorm_le hN
    intro β
    simpa only [hφ, Fintype.card_fin] using htest β
  · simpa only [hφ, Fintype.card_fin] using happrox

end Erdos335.IntermediateScale
