import Erdos335.CompactSumLocalization
import Erdos335.LoebCompactEqualityReduction
import Erdos335.LoebQuotientDifference

/-!
# Sumset equality and localization through a compact factor
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem ae_map_set_eq_of_preimage
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (C D : Set Y) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hpre : f ⁻¹' C =ᵐ[μ] f ⁻¹' D) : C =ᵐ[Measure.map f μ] D := by
  have hmeas : MeasurableSet {x | (x ∈ C) = (x ∈ D)} := by
    have hset : {x | (x ∈ C) = (x ∈ D)} = {x | x ∈ C ↔ x ∈ D} := by
      ext x
      exact eq_iff_iff
    rw [hset]
    exact hC.iff hD
  exact (ae_map_iff hf.aemeasurable hmeas).2 hpre

local instance compactSumTransferLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem compact_factor_shrinking_sumsets_localize
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [PolishSpace K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableAdd₂ K] [MeasurableNeg K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (S : Set K) (hS : MeasurableSet S)
    (hperiod : ∀ z : K, z +ᵥ S =ᵐ[Measure.map φ (loebMeasure U hU)] S → z = 0)
    (A B : ℕ → Set K) (hAB : ∀ n, MeasurableSet (A n + B n))
    (hsum : ∀ n, (φ ⁻¹' A n) + (φ ⁻¹' B n) =ᵐ[loebMeasure U hU] φ ⁻¹' S)
    (hmass : Tendsto (fun n => (Measure.map φ (loebMeasure U hU) (A n)).toReal)
      atTop (𝓝 (Measure.map φ (loebMeasure U hU) S).toReal))
    (V : Set K) (hV : V ∈ 𝓝 (0 : K)) :
    ∀ᶠ n in atTop, B n - B n ⊆ V := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure ν := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have : ν.IsNegInvariant := loebMeasure_map_hom_isNegInvariant U hU q φ hφ
  have hsum' (n : ℕ) : A n + B n =ᵐ[ν] S := by
    apply ae_map_set_eq_of_preimage μ φ hφ (A n + B n) S (hAB n) hS
    rw [preimage_add_of_surjective_addHom φ hsurj (A n) (B n)]
    exact hsum n
  exact shrinking_sumsets_localize ν S hS hperiod A B (fun n => (hsum' n).le) hmass V hV

end Erdos335.Loeb

end
