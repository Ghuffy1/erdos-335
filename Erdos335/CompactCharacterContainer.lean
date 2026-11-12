import Erdos335.CircleNormArg
import Erdos335.CircleCharacterMeasure
import Erdos335.CompactCharacterGrowth

/-!
# Invariant containers with measure controlled by a critical summand
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem exists_character_invariant_containers
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [ConnectedSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (S : Set G) (hS : MeasurableSet S)
    (hperiod : ∀ t : G, t +ᵥ S =ᵐ[μ] S → t = 0)
    (φ : G →+ AddCircle (1 : ℝ)) (hφ : Continuous φ) (hne : φ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : Set G, B.Nonempty → (A + B ≤ᵐ[μ] S) →
      (μ S).toReal = (μ A).toReal + (μ B).toReal →
      ∃ T : Set G, MeasurableSet T ∧ B ⊆ T ∧
        (∀ h : φ.ker, (h : G) +ᵥ T = T) ∧ (μ T).toReal ≤ C * (μ B).toReal := by
  let χ : AddChar G Circle := AddCircle.toCircle_addChar.compAddMonoidHom φ
  have hχ : Continuous χ := AddCircle.continuous_toCircle.comp hφ
  obtain ⟨ε, hε, hbound⟩ := exists_character_width_mass_bound μ S hS hperiod χ hχ
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hsurj := continuous_circle_hom_surjective_of_ne_zero φ hφ hne
  refine ⟨1 / ε, one_div_pos.mpr hε, ?_⟩
  intro A B hB hsum hmass
  obtain ⟨b, hb⟩ := hB
  let r : ℝ := (μ B).toReal / (2 * ε)
  let T : Set G := φ ⁻¹' Metric.closedBall (φ b) r
  have hTm : MeasurableSet T := measurableSet_closedBall.preimage hφ.measurable
  have hBT : B ⊆ T := by
    intro x hx
    have hwidth := hbound A B hsum x hx b hb
    rw [hmass] at hwidth
    have hnorm := norm_unitAddCircle_eq_arg (φ (x - b))
    have harg : |Complex.arg (AddCircle.toCircle (φ (x - b)) : ℂ)| ≤
        Real.pi * (μ B).toReal / ε := by
      change ε * |Complex.arg (AddCircle.toCircle (φ (x - b)) : ℂ)| ≤ _ at hwidth
      apply (le_div_iff₀ hε).mpr
      nlinarith
    change dist (φ x) (φ b) ≤ r
    rw [dist_eq_norm, ← map_sub, hnorm]
    dsimp [r]
    apply (div_le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)
      (mul_pos (by norm_num) hε)).mpr
    have := (le_div_iff₀ hε).mp harg
    nlinarith [Real.pi_pos]
  have hperiodT (h : φ.ker) : (h : G) +ᵥ T = T := by
    ext x
    change (∃ y, φ y ∈ Metric.closedBall (φ b) r ∧ (h : G) + y = x) ↔
      φ x ∈ Metric.closedBall (φ b) r
    have hh : φ (h : G) = 0 := h.property
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [map_add, hh, zero_add] using hy
    · intro hx
      refine ⟨x - h, ?_, by abel⟩
      simpa only [map_sub, hh, sub_zero] using hx
  refine ⟨T, hTm, hBT, hperiodT, ?_⟩
  have hr : 0 ≤ r := div_nonneg ENNReal.toReal_nonneg (mul_pos (by norm_num) hε).le
  have hmeasure := measure_character_closedBall_preimage_le μ φ hφ hsurj (φ b) r hr
  change (μ T).toReal ≤ _ at hmeasure
  calc
    (μ T).toReal ≤ 2 * r := hmeasure
    _ = (1 / ε) * (μ B).toReal := by dsimp [r]; field_simp

end Erdos335.Loeb
