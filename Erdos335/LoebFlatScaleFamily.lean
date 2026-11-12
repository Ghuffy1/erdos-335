import Erdos335.LoebRegularStructuredFamily
import Erdos335.PositiveIntermediateScales
import Erdos335.UnitIntervalFlatness

/-!
# A flat structured fiber inside a prescribed growing scale gap

The construction follows the Hilbert-space part of the intermediate-scale
regularity argument of Ackelsberg and Richter. The scale formula uses the
ratio of the prescribed endpoints so that lexicographic separation holds
throughout an arbitrary growing gap.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Erdos335.Loeb

open Erdos335.IntermediateScale

theorem exists_loeb_flat_scale_family
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (F : ℕ → ℝ) (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (ε : ℕ → ℝ) (L : ℕ → ℕ)
      (m : ∀ (p : BlockScaleParameter) (k s : ℕ),
        BlockRegularModel F (blockScaleFamily lower upper p s) (L k) (ε k))
      (g : BlockScaleParameter → Lp ℝ 2 (loebMeasure (X := fun s => Fin (N s)) U hU))
      (x : unitInterval),
      (x : ℝ) ∈ Ioo (0 : ℝ) 1 ∧
      (∀ k, 0 < ε k ∧ ε k ≤ 1 ∧ 0 < L k) ∧
      Tendsto ε atTop (𝓝 0) ∧
      (∀ k l, k < l → (L k : ℝ) * ε l ≤ ε k) ∧
      (∀ p, Tendsto (fun k => prefixLoebVector N U hU (stitchedBlockValue N hN (m p k))
        (stitchedBlockValue_mem N hN (m p k))) atTop (𝓝 (g p))) ∧
      (∀ p, ‖g p‖ ≤ 1) ∧
      (∀ p, ⟪g p, prefixLoebVector N U hU F hF - g p⟫_ℝ = 0) ∧
      (∀ p q, p ≤ q → ⟪g q, prefixLoebVector N U hU F hF - g p⟫_ℝ = 0) ∧
      ∀ η : unitInterval, g (toLex (x, η)) = g (toLex (x, 0)) := by
  obtain ⟨ε, L, m, g, hpos, hε, hbudget, hlim, hnorm, hown, hcross, _horder⟩ :=
    exists_loeb_regular_structured_family N hN hmono hprev
      (blockScaleFamily lower upper) (blockScaleFamily_pos lower upper)
      (blockScaleFamily_ambient_ratio lower upper N hlower hupper hgap hupperN)
      (blockScaleFamily_separated lower upper hlower hgap) F hF U hU
  have hfiber (x t u : unitInterval) (htu : t ≤ u) :
      ⟪g (toLex (x, u)), prefixLoebVector N U hU F hF - g (toLex (x, t))⟫_ℝ = 0 := by
    exact hcross _ _ (Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, htu⟩))
  have hbetween (x y : unitInterval) (hxy : x < y) :
      ⟪g (toLex (y, 0)), prefixLoebVector N U hU F hF - g (toLex (x, 1))⟫_ℝ = 0 := by
    exact hcross _ _ (Prod.Lex.toLex_le_toLex.mpr (Or.inl hxy))
  obtain ⟨x, hx, hflat⟩ := exists_flat_unitInterval_structured_fiber
    (prefixLoebVector N U hU F hF) (fun x t => g (toLex (x, t)))
    (fun x t => hown _) hfiber hbetween
  exact ⟨ε, L, m, g, x, hx, hpos, hε, hbudget, hlim, hnorm, hown, hcross, hflat⟩

end Erdos335.Loeb
