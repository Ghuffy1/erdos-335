import Erdos335.RemovalParameters
import Mathlib.Order.Filter.Finite

/-!
# Slowly increasing indices preserving eventual finite requirements
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Classical

namespace Erdos335.IntermediateScale

theorem exists_slow_index_for_eventual_property (P : ℕ → ℕ → Prop)
    (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ (∀ n, k n ≤ n) ∧
      ∀ᶠ n in atTop, P (k n) n := by
  have hthreshold (j : ℕ) : ∃ N : ℕ, ∀ n ≥ N, P j n := eventually_atTop.mp (hP j)
  choose N hN using hthreshold
  let M := fun j => max j (N j)
  let k := fun n => Nat.findGreatest (fun j => M j ≤ n) n
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop (M j)] with n hn
    exact Nat.le_findGreatest ((le_max_left j (N j)).trans hn) hn
  refine ⟨k, hk, fun n => Nat.findGreatest_le n, ?_⟩
  filter_upwards [eventually_ge_atTop (M 0)] with n hn
  have hkn : M (k n) ≤ n := Nat.findGreatest_spec (P := fun j => M j ≤ n) (Nat.zero_le n) hn
  exact hN (k n) n ((le_max_right _ _).trans hkn)

theorem exists_slow_diagonal_for_finite_requirements (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ l k, k ≤ l → ∀ᶠ n in atTop, P k l n) :
    ∃ l : ℕ → ℕ, Tendsto l atTop atTop ∧ (∀ n, l n ≤ n) ∧
      ∀ᶠ n in atTop, ∀ k ≤ l n, P k (l n) n := by
  have hfinite (l : ℕ) : ∀ᶠ n in atTop, ∀ k ≤ l, P k l n := by
    have h := (eventually_all_finset (range (l + 1))).mpr
      (fun k hk => hP l k (by simpa using mem_range.mp hk))
    exact h.mono fun n hn k hk => hn k (mem_range.mpr (by omega))
  exact exists_slow_index_for_eventual_property (fun l n => ∀ k ≤ l, P k l n) hfinite

end Erdos335.IntermediateScale
