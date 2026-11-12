import Erdos335.OrdinaryDensityLocalModel
import Erdos335.LoebRegularGlobalMask
import Erdos335.LoebRegularPairWindowInverse
import Erdos335.LoebRegularActualWindowInverse

/-!
# A regular summand forces an ordinary periodic summand
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335

theorem exists_periodic_summand_of_regular_capacity
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hdA : HasDensity A a) (hdB : HasDensity B b)
    (hdC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (happroxA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε) :
    (∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))), DensityEquivalent A (periodicSet R)) ∨
    (∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))), DensityEquivalent B (periodicSet R)) := by
  classical
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨q, start, D, E, hdiv, hq, hDsub, hDAE, hEsub, hexhaust, hmA, hmB, hmC, hmE, hsum⟩ :=
    exists_ordinary_density_loeb_models U hU A B a b (a + b) hdA hdB hdC
  by_cases happroxB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) B).card : ℝ) / (k : ℕ) ≤ b + ε
  · rcases Loeb.loeb_regular_pair_window_inverse U hU q hdiv hq A B start a b ha hb D E
      hDsub hDAE hEsub hexhaust hmA hmB hmC hmE hsum hgap happroxA happroxB with
        ⟨h, R, _, hmask⟩ | ⟨h, R, _, hmask⟩
    · obtain ⟨S, hS⟩ := Loeb.loeb_regular_natural_window_global_mask U hU q hdiv A start a hA
        hdA hmA happroxA h R hmask
      exact Or.inl ⟨h, S, hS⟩
    · obtain ⟨T, hT⟩ := Loeb.loeb_regular_natural_window_global_mask U hU q hdiv B start b hB
        hdB hmB happroxB h R hmask
      exact Or.inr ⟨h, T, hT⟩
  · push_neg at happroxB
    obtain ⟨δ, hδ, hcapacity⟩ := happroxB
    obtain ⟨h, R, _, hmask⟩ := Loeb.loeb_regular_actual_window_is_periodic U hU q hdiv hq A B start
      a b δ ha hb hδ D E hDsub hDAE hEsub hexhaust hmA hmB hmC hmE hsum hgap
      (fun k => (hcapacity k).le) happroxA
    obtain ⟨S, hS⟩ := Loeb.loeb_regular_natural_window_global_mask U hU q hdiv A start a hA
      hdA hmA happroxA h R hmask
    exact Or.inl ⟨h, S, hS⟩

end Erdos335

end
