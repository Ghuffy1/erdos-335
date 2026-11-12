import Erdos335.LoebBlockStructuredFamily
import Erdos335.BlockRegularitySequence

/-!
# Existence of nested structured limits for separated block scales
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Erdos335.Loeb

open Erdos335.IntermediateScale

theorem exists_loeb_regular_structured_family
    {P : Type*} [LinearOrder P]
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (H : P → ℕ → ℕ) (hH : ∀ p s, 0 < H p s)
    (hHN : ∀ p, Tendsto (fun s => (H p s : ℝ) / N s) atTop (𝓝 0))
    (hsep : ∀ p q, p < q → Tendsto (fun s => (H p s : ℝ) / H q s) atTop (𝓝 0))
    (F : ℕ → ℝ) (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (ε : ℕ → ℝ) (L : ℕ → ℕ)
      (m : ∀ p k s, BlockRegularModel F (H p s) (L k) (ε k))
      (g : P → Lp ℝ 2 (loebMeasure (X := fun s => Fin (N s)) U hU)),
      (∀ k, 0 < ε k ∧ ε k ≤ 1 ∧ 0 < L k) ∧
      Tendsto ε atTop (𝓝 0) ∧
      (∀ k l, k < l → (L k : ℝ) * ε l ≤ ε k) ∧
      (∀ p, Tendsto (fun k => prefixLoebVector N U hU (stitchedBlockValue N hN (m p k))
        (stitchedBlockValue_mem N hN (m p k))) atTop (𝓝 (g p))) ∧
      (∀ p, ‖g p‖ ≤ 1) ∧
      (∀ p, ⟪g p, prefixLoebVector N U hU F hF - g p⟫_ℝ = 0) ∧
      (∀ p q, p ≤ q → ⟪g q, prefixLoebVector N U hU F hF - g p⟫_ℝ = 0) ∧
      ∀ p q, p ≤ q → ‖g q‖ ≤ ‖g p‖ := by
  classical
  obtain ⟨ε, L, hpos, hε, hbudget, hex⟩ := exists_block_regularity_sequence F hF
  let m (p : P) (k s : ℕ) : BlockRegularModel F (H p s) (L k) (ε k) :=
    Classical.choice (hex k (H p s) (hH p s))
  obtain ⟨g, hlim, hnorm, hown, hcross, horder⟩ := exists_loeb_block_structured_family
    N hN hmono hprev H hH hHN hsep F hF ε L
    (fun k => (hpos k).1.le) (fun k => (hpos k).2.1) hε hbudget m U hU
  exact ⟨ε, L, m, g, hpos, hε, hbudget, hlim, hnorm, hown, hcross, horder⟩

end Erdos335.Loeb
