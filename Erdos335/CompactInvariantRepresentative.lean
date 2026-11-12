import Erdos335.CompactSubgroupAverage
import Erdos335.CompactDysonTransform

/-!
# Measurable representatives invariant under a measured subgroup
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem exists_exact_invariant_ae_set
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableAdd₂ G] [MeasurableAdd₂ H]
    (μ : Measure G) [IsFiniteMeasure μ]
    (ν : Measure H) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant]
    (φ : H →+ G) (hφ : Measurable φ) (S : Set G) (hS : MeasurableSet S)
    (hperiod : ∀ h : H, φ h +ᵥ S =ᵐ[μ] S) :
    ∃ T : Set G, MeasurableSet T ∧ T =ᵐ[μ] S ∧ ∀ h : H, φ h +ᵥ T = T := by
  classical
  let f := S.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hS
  have hfperiod (h : H) : (fun x => f (x + φ h)) =ᵐ[μ] f := by
    filter_upwards [hperiod (-h)] with x hx
    have hmem : (x + φ h ∈ S) = (x ∈ S) := by
      have heq : (x ∈ φ (-h) +ᵥ S) = (x + φ h ∈ S) := by
        rw [vadd_set_eq_neg_preimage]
        simp only [mem_preimage, map_neg, neg_neg, add_comm]
      exact heq.symm.trans hx
    simp only [f, Set.indicator_apply]
    rw [hmem]
  obtain ⟨g, hgm, hgae, hgperiod⟩ := exists_exact_invariant_ae_average μ ν φ hφ f hf hfperiod
  let T := {x : G | (1 / 2 : ℝ) < g x}
  have hTm : MeasurableSet T := measurableSet_lt measurable_const hgm
  have hTae : T =ᵐ[μ] S := by
    filter_upwards [hgae] with x hx
    change ((1 / 2 : ℝ) < g x) = (x ∈ S)
    rw [hx]
    by_cases hxs : x ∈ S <;> norm_num [f, hxs]
  refine ⟨T, hTm, hTae, ?_⟩
  intro h
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (1 / 2 : ℝ) < g (φ h + y)
    rw [add_comm, hgperiod]
    exact hy
  · intro hx
    refine ⟨x - φ h, ?_, by simp [vadd_eq_add]⟩
    have heq : g (x - φ h) = g x := by
      simpa only [map_neg, sub_eq_add_neg] using hgperiod (-h) x
    change (1 / 2 : ℝ) < g (x - φ h)
    rw [heq]
    exact hx

end Erdos335.Loeb

end
