import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

/-!
# Localization from a unique maximum on a compact group

The compact inverse proof applies this to the overlap of a sumset with
its translates. A trivial essential stabilizer gives the unique maximum.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Loeb

theorem eventually_difference_subset_of_unique_maximum
    {G : Type*} [AddGroup G] [TopologicalSpace G] [CompactSpace G]
    (f : G → ℝ) (hf : Continuous f) (hstrict : ∀ x, x ≠ 0 → f x < f 0)
    (mass : ℕ → ℝ) (hmass : Tendsto mass atTop (𝓝 (f 0)))
    (B : ℕ → Set G)
    (hbound : ∀ n, ∀ x ∈ B n, ∀ y ∈ B n, mass n ≤ f (x - y))
    (U : Set G) (hU : U ∈ 𝓝 (0 : G)) :
    ∀ᶠ n in atTop, B n - B n ⊆ U := by
  obtain ⟨V, hVU, hVopen, hzero⟩ := mem_nhds_iff.mp hU
  by_cases hnonempty : Vᶜ.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hVopen.isClosed_compl.isCompact.exists_isMaxOn hnonempty hf.continuousOn
    have hz0 : z ≠ 0 := fun heq => hz (heq ▸ hzero)
    have hsmall := (tendsto_order.mp hmass).1 (f z) (hstrict z hz0)
    filter_upwards [hsmall] with n hn
    rintro w ⟨x, hx, y, hy, rfl⟩
    apply hVU
    by_contra houtside
    exact (not_lt_of_ge ((hbound n x hx y hy).trans (hmax houtside))) hn
  · filter_upwards with n
    intro w _
    apply hVU
    by_contra houtside
    exact hnonempty ⟨w, houtside⟩

end Erdos335.Loeb
