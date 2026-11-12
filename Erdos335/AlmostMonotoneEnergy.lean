import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Convergence of bounded energies with vanishing monotonicity error
-/

set_option autoImplicit false

open Filter Topology Set

namespace Erdos335.IntermediateScale

theorem cauchy_of_almost_monotone (a e : ℕ → ℝ)
    (hbounded : BddAbove (range a)) (he : Tendsto e atTop (𝓝 0))
    (horder : ∀ k l, k ≤ l → a k ≤ a l + e k) : CauchySeq a := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (he.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 4 by positivity)))
  let S := a '' Ici K
  have hS : S.Nonempty := ⟨a K, K, mem_Ici.mpr le_rfl, rfl⟩
  have hbS : BddAbove S := hbounded.mono (image_subset_range _ _)
  obtain ⟨_, ⟨k, hk, rfl⟩, hnear⟩ := exists_lt_of_lt_csSup hS
    (show sSup S - ε / 4 < sSup S by linarith)
  change K ≤ k at hk
  refine ⟨k, fun i hi j hj => ?_⟩
  have hui : a i ≤ sSup S := le_csSup hbS ⟨i, mem_Ici.mpr (hk.trans hi), rfl⟩
  have huj : a j ≤ sSup S := le_csSup hbS ⟨j, mem_Ici.mpr (hk.trans hj), rfl⟩
  have hli := horder k i hi
  have hlj := horder k j hj
  have hek := hK k hk
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

theorem tendsto_of_almost_monotone (a e : ℕ → ℝ)
    (hbounded : BddAbove (range a)) (he : Tendsto e atTop (𝓝 0))
    (horder : ∀ k l, k ≤ l → a k ≤ a l + e k) :
    ∃ A : ℝ, Tendsto a atTop (𝓝 A) :=
  cauchySeq_tendsto_of_complete (cauchy_of_almost_monotone a e hbounded he horder)

end Erdos335.IntermediateScale
