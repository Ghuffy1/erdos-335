import Erdos335.CompactCharacterDensity
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Uniform circle polynomial approximation
-/

set_option autoImplicit false

open Set
open scoped Topology BigOperators

namespace Erdos335.IntermediateScale

noncomputable def circleMonomial (n : ℤ) : C(Circle, ℂ) :=
  ⟨fun z => (z ^ n : Circle), by
    exact (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))).zpow₀ n
      (fun z => Or.inl (Circle.coe_ne_zero z))⟩

theorem circleMonomial_span_dense :
    (Submodule.span ℂ (Set.range circleMonomial)).topologicalClosure = ⊤ := by
  apply Loeb.separating_multiplicative_span_dense
  · refine ⟨0, ?_⟩
    ext z
    simp [circleMonomial]
  · rintro f ⟨m, rfl⟩ g ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext z
    simp [circleMonomial, zpow_add]
  · rintro f ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    ext z
    change ((z ^ (-n) : Circle) : ℂ) = star ((z ^ n : Circle) : ℂ)
    rw [zpow_neg, Circle.coe_inv_eq_conj]
    rfl
  · intro x y hxy
    refine ⟨circleMonomial 1, ⟨1, rfl⟩, ?_⟩
    intro h
    apply hxy
    apply Subtype.ext
    simpa [circleMonomial] using h

theorem exists_circle_polynomial_approximation (F : C(Circle, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : Finset ℤ) (w : ℤ → ℂ), ∀ z : Circle,
      ‖F z - ∑ n ∈ S, w n * (z : ℂ) ^ n‖ < ε := by
  have hclosure : F ∈ closure (Submodule.span ℂ (Set.range circleMonomial) : Set C(Circle, ℂ)) := by
    change F ∈ (Submodule.span ℂ (Set.range circleMonomial)).topologicalClosure
    rw [circleMonomial_span_dense]
    trivial
  obtain ⟨P, hP, hdist⟩ := Metric.mem_closure_iff.mp hclosure ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hP
  have heval (z : Circle) : P z = ∑ n ∈ c.support, c n * (z : ℂ) ^ n := by
    rw [← hc]
    simp [Finsupp.sum, circleMonomial]
  refine ⟨c.support, c, ?_⟩
  intro z
  have hpoint := (ContinuousMap.dist_apply_le_dist z (f := F) (g := P)).trans_lt hdist
  simpa only [dist_eq_norm, heval] using hpoint

end Erdos335.IntermediateScale
