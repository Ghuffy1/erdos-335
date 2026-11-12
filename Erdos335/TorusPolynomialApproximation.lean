import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Uniform finite Fourier approximation on a finite-dimensional torus
-/

set_option autoImplicit false

open Set
open scoped Topology BigOperators

namespace Erdos335.IntermediateScale

theorem exists_torus_polynomial_approximation {I : Type*} [Fintype I]
    (F : C(UnitAddTorus I, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : Finset (I → ℤ)) (c : (I → ℤ) → ℂ), ∀ x : UnitAddTorus I,
      ‖F x - ∑ n ∈ S, c n * UnitAddTorus.mFourier n x‖ < ε := by
  have hclosure : F ∈ closure (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := I))) :
      Set C(UnitAddTorus I, ℂ)) := by
    change F ∈ (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := I)))).topologicalClosure
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    trivial
  obtain ⟨P, hP, hdist⟩ := Metric.mem_closure_iff.mp hclosure ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hP
  have heval (x : UnitAddTorus I) : P x = ∑ n ∈ c.support, c n * UnitAddTorus.mFourier n x := by
    rw [← hc]
    simp [Finsupp.sum]
  refine ⟨c.support, c, fun x => ?_⟩
  have hpoint := (ContinuousMap.dist_apply_le_dist x (f := F) (g := P)).trans_lt hdist
  simpa only [dist_eq_norm, heval] using hpoint

end Erdos335.IntermediateScale
