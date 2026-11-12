import Erdos335.LoebRealBounds
import Erdos335.PrefixEnergyAlgebra

/-!
# Real Loeb vectors of ordinary functions on growing integer prefixes
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Erdos335.Loeb

variable (N : ℕ → ℕ) [∀ s, NeZero (N s)]

noncomputable def prefixLoebVector (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ℕ → ℝ) (hf : ∀ n, f n ∈ Icc (0 : ℝ) 1) :
    Lp ℝ 2 (loebMeasure (X := fun s => Fin (N s)) U hU) :=
  realLoebVector U hU (fun s (n : Fin (N s)) => f n.val) (fun s n => hf n.val)

theorem tendsto_prefixLoebVector_energy (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ℕ → ℝ) (hf : ∀ n, f n ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun s => Erdos335.IntermediateScale.prefixEnergy f (N s)) (U : Filter ℕ)
      (𝓝 (‖prefixLoebVector N U hU f hf‖ ^ 2)) := by
  simpa only [Erdos335.IntermediateScale.prefixEnergy, prefixLoebVector,
    Nat.card_eq_fintype_card, Fintype.card_fin, Finset.sum_range] using
    tendsto_realLoebVector_energy U hU (fun s (n : Fin (N s)) => f n.val) (fun s n => hf n.val)

theorem tendsto_prefixLoebVector_residual_correlation
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (F f g : ℕ → ℝ)
    (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1) (hf : ∀ n, f n ∈ Icc (0 : ℝ) 1)
    (hg : ∀ n, g n ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun s => Erdos335.IntermediateScale.prefixCorrelation f (fun n => F n - g n) (N s))
      (U : Filter ℕ)
      (𝓝 ⟪prefixLoebVector N U hU f hf,
        prefixLoebVector N U hU F hF - prefixLoebVector N U hU g hg⟫_ℝ) := by
  simpa only [Erdos335.IntermediateScale.prefixCorrelation, prefixLoebVector,
    Nat.card_eq_fintype_card, Fintype.card_fin, Finset.sum_range] using
    tendsto_realLoebVector_residual_correlation U hU
      (fun s (n : Fin (N s)) => F n.val) (fun s (n : Fin (N s)) => f n.val)
      (fun s (n : Fin (N s)) => g n.val)
      (fun s n => hF n.val) (fun s n => hf n.val) (fun s n => hg n.val)

end Erdos335.Loeb
