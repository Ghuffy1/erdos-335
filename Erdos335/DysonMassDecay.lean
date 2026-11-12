import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Decay under the Dyson mass inequality
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335.Loeb

theorem dyson_mass_tendsto_zero (b : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) ≤ (1 - b n) * b n) :
    Tendsto b atTop (𝓝 0) := by
  have hanti : Antitone b := antitone_nat_of_succ_le (fun n => by
    have h := hstep n
    nlinarith [sq_nonneg (b n)])
  have hbounded : BddBelow (Set.range b) := ⟨0, by rintro x ⟨n, rfl⟩; exact hnonneg n⟩
  let a := ⨅ n, b n
  have hlim : Tendsto b atTop (𝓝 a) := tendsto_atTop_ciInf hanti hbounded
  have hlimNext : Tendsto (fun n => b (n + 1)) atTop (𝓝 a) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have halower : 0 ≤ a := ge_of_tendsto hlim (Eventually.of_forall hnonneg)
  have haupper : a ≤ (1 - a) * a := le_of_tendsto_of_tendsto hlimNext
    ((tendsto_const_nhds.sub hlim).mul hlim) (Eventually.of_forall hstep)
  have ha : a = 0 := by nlinarith [sq_nonneg a]
  exact ha ▸ hlim

end Erdos335.Loeb
