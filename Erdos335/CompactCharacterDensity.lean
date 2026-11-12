import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Density of a separating multiplicative family

A conjugation-stable multiplicative family of continuous complex functions
which contains the constants and separates points has dense linear span.
This form of Stone-Weierstrass is suited to internal character families.
-/

set_option autoImplicit false

open Set Submodule
open scoped Topology ENNReal

namespace Erdos335.Loeb

theorem separating_multiplicative_span_dense
    {G : Type*} [TopologicalSpace G] [CompactSpace G]
    (S : Set C(G, ℂ)) (hone : (1 : C(G, ℂ)) ∈ S)
    (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hstar : ∀ f ∈ S, star f ∈ S)
    (hsep : ∀ x y : G, x ≠ y → ∃ f ∈ S, f x ≠ f y) :
    (Submodule.span ℂ S).topologicalClosure = ⊤ := by
  let A : StarSubalgebra ℂ C(G, ℂ) := {
    toSubalgebra := Algebra.adjoin ℂ S
    star_mem' := by
      change Algebra.adjoin ℂ S ≤ star (Algebra.adjoin ℂ S)
      apply Algebra.adjoin_le
      intro f hf
      exact Algebra.subset_adjoin (hstar f hf)
  }
  have hspan : A.toSubalgebra.toSubmodule = Submodule.span ℂ S := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans ?_ Submodule.subset_span
    intro f hf
    exact Submonoid.closure_induction (fun _ h => h) hone
      (fun f g _ _ hf hg => hmul f hf g hg) hf
  have hAsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hneq⟩ := hsep x y hxy
    exact ⟨_, ⟨f, Algebra.subset_adjoin hf, rfl⟩, hneq⟩
  have hA := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hAsep
  rw [← hspan]
  exact congrArg (fun B : StarSubalgebra ℂ C(G, ℂ) => B.toSubalgebra.toSubmodule) hA

theorem separating_multiplicative_Lp_span_dense
    {G : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.WeaklyRegular] [MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (S : Set C(G, ℂ)) (hone : (1 : C(G, ℂ)) ∈ S)
    (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hstar : ∀ f ∈ S, star f ∈ S)
    (hsep : ∀ x y : G, x ≠ y → ∃ f ∈ S, f x ≠ f y) :
    (Submodule.span ℂ ((ContinuousMap.toLp p μ ℂ) '' S)).topologicalClosure = ⊤ := by
  have hdense := separating_multiplicative_span_dense S hone hmul hstar hsep
  have hmap := (ContinuousMap.toLp_denseRange ℂ μ ℂ hp).topologicalClosure_map_submodule hdense
  simpa only [Submodule.map_span, ContinuousLinearMap.coe_coe] using hmap

theorem separating_multiplicative_L2_ext
    {G : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.WeaklyRegular] [MeasureTheory.IsFiniteMeasure μ]
    (S : Set C(G, ℂ)) (hone : (1 : C(G, ℂ)) ∈ S)
    (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hstar : ∀ f ∈ S, star f ∈ S)
    (hsep : ∀ x y : G, x ≠ y → ∃ f ∈ S, f x ≠ f y)
    (f g : MeasureTheory.Lp ℂ 2 μ)
    (hcoeff : ∀ ψ ∈ S,
      inner ℂ (ContinuousMap.toLp 2 μ ℂ ψ) f = inner ℂ (ContinuousMap.toLp 2 μ ℂ ψ) g) :
    f = g := by
  have hdense := separating_multiplicative_Lp_span_dense μ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    S hone hmul hstar hsep
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr hdense
  apply hd.eq_of_inner_right ℂ
  intro v hv
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hv
  · intro ψ hψ
    obtain ⟨k, hk, rfl⟩ := hψ
    exact hcoeff k hk
  · intros
    simp_all only [inner_add_left]
  · intros
    simp_all only [inner_smul_left]

end Erdos335.Loeb
