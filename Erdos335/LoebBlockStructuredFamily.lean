import Erdos335.LoebPrefixVectors
import Erdos335.StrictStructuredFamily
import Erdos335.AnnularCrossCorrelation

/-!
# Nested Loeb structured components assembled from block models
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Erdos335.Loeb

open Erdos335.IntermediateScale

theorem exists_loeb_block_structured_family
    {P : Type*} [LinearOrder P]
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (H : P → ℕ → ℕ) (hH : ∀ p s, 0 < H p s)
    (hHN : ∀ p, Tendsto (fun s => (H p s : ℝ) / N s) atTop (𝓝 0))
    (hsep : ∀ p q, p < q → Tendsto (fun s => (H p s : ℝ) / H q s) atTop (𝓝 0))
    (F : ℕ → ℝ) (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (ε : ℕ → ℝ) (L : ℕ → ℕ)
    (hε0 : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hε : Tendsto ε atTop (𝓝 0))
    (hbudget : ∀ k l, k < l → (L k : ℝ) * ε l ≤ ε k)
    (m : ∀ p k s, BlockRegularModel F (H p s) (L k) (ε k))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ g : P → Lp ℝ 2 (loebMeasure (X := fun s => Fin (N s)) U hU),
      (∀ p, Tendsto (fun k => prefixLoebVector N U hU (stitchedBlockValue N hN (m p k))
        (stitchedBlockValue_mem N hN (m p k))) atTop (𝓝 (g p))) ∧
      (∀ p, ‖g p‖ ≤ 1) ∧
      (∀ p, ⟪g p, prefixLoebVector N U hU F hF - g p⟫_ℝ = 0) ∧
      (∀ p q, p ≤ q → ⟪g q, prefixLoebVector N U hU F hF - g p⟫_ℝ = 0) ∧
      ∀ p q, p ≤ q → ‖g q‖ ≤ ‖g p‖ := by
  let : MeasurableSpace ((U : Filter ℕ).Product (fun s => Fin (N s))) := loebMeasurableSpace U
  apply exists_hilbert_strict_structured_family (prefixLoebVector N U hU F hF)
    (fun p k => prefixLoebVector N U hU (stitchedBlockValue N hN (m p k))
      (stitchedBlockValue_mem N hN (m p k))) (fun k => 2 * ε k)
  · intro p k
    exact realLoebVector_norm_le_one U hU _ _
  · intro p k
    have ht := tendsto_prefixLoebVector_residual_correlation N U hU F
      (stitchedBlockValue N hN (m p k)) (stitchedBlockValue N hN (m p k))
      hF (stitchedBlockValue_mem N hN (m p k)) (stitchedBlockValue_mem N hN (m p k))
    exact tendsto_nhds_unique ht
      ((stitchedBlock_orthogonality N hN hmono hprev (hHN p) (hH p) (m p k) hF).mono_left hU)
  · exact fun k => mul_nonneg (by norm_num) (hε0 k)
  · simpa only [mul_zero] using hε.const_mul 2
  · intro p q hpq k l hkl
    have hscale : H p = H q ∨ Tendsto (fun s => (H p s : ℝ) / H q s) atTop (𝓝 0) := by
      rcases hpq.eq_or_lt with heq | hlt
      · exact Or.inl (congrArg H heq)
      · exact Or.inr (hsep p q hlt)
    obtain ⟨e, he, hb⟩ := stitched_models_correlation_bound N hN hmono hprev hF
      (m q k) (m p l) (hH q) (hH p) (hε0 k) (hε0 l) (hε1 l) hscale (hHN q)
    have ht := (tendsto_prefixLoebVector_residual_correlation N U hU F
      (stitchedBlockValue N hN (m q k)) (stitchedBlockValue N hN (m p l))
      hF (stitchedBlockValue_mem N hN (m q k)) (stitchedBlockValue_mem N hN (m p l))).abs.sub
      (he.mono_left hU)
    simp only [sub_zero] at ht
    apply le_of_tendsto ht
    filter_upwards [hb.filter_mono hU] with s hs
    linarith [hbudget k l hkl]

end Erdos335.Loeb
