import Erdos335.CircleArcSupport
import Erdos335.LoebHaar
import Erdos335.StabilizerPullback

/-!
# Literal point constraints from an almost-everywhere compact sum container
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance compactSupportLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_add_support_subset_of_ae_sum_container
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableAdd₂ K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (D L : Set K) (hD : MeasurableSet D) (hL : IsClosed L)
    (hBmodel : B =ᵐ[loebMeasure U hU] φ ⁻¹' D)
    (hsum : A + B ≤ᵐ[loebMeasure U hU] φ ⁻¹' L)
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (ha : a ∈ A) :
    φ a +ᵥ ((Measure.map φ (loebMeasure U hU)).restrict D).support ⊆ L := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : MeasurableAdd G := {
    measurable_const_add := measurable_add_left U hU
    measurable_add_const := fun c => by
      simpa only [add_comm] using measurable_add_left U hU c }
  have : μ.IsAddLeftInvariant := ⟨fun t => loebMeasure_map_add_left U hU t⟩
  have hshift := (measurePreserving_add_left μ a).quasiMeasurePreserving.ae hsum
  let T := (-φ a) +ᵥ L
  have hTclosed : IsClosed T := by
    rw [show T = (-φ a) +ᵥ L from rfl, vadd_set_eq_neg_preimage]
    exact hL.preimage (continuous_const.add continuous_id)
  have hpre : φ ⁻¹' D ≤ᵐ[μ] φ ⁻¹' T := by
    filter_upwards [hshift, hBmodel] with b hb hbmodel hbD
    have hbB : b ∈ B := hbmodel.mpr hbD
    have h := hb ⟨a, ha, b, hbB, rfl⟩
    change φ (a + b) ∈ L at h
    change φ b ∈ T
    dsimp [T]
    rw [vadd_set_eq_neg_preimage]
    simpa only [mem_preimage, neg_neg, map_add] using h
  have hpred : MeasurableSet {x : K | x ∈ D → x ∈ T} := by
    convert hD.compl.union hTclosed.measurableSet using 1
    ext x
    simp only [mem_setOf_eq, mem_union, mem_compl_iff]
    tauto
  have hcompact : D ≤ᵐ[ν] T := (ae_map_iff hφ.aemeasurable hpred).2 hpre
  have hmem : T ∈ ae (ν.restrict D) := by
    change ∀ᵐ x ∂ν.restrict D, x ∈ T
    rw [ae_restrict_iff' hD]
    exact hcompact
  have hsupport := Measure.support_subset_of_isClosed hTclosed hmem
  rintro x ⟨b, hb, rfl⟩
  have h := hsupport hb
  dsimp [T] at h
  rw [vadd_set_eq_neg_preimage] at h
  simpa only [mem_preimage, neg_neg, vadd_eq_add] using h

end Erdos335.Loeb

end
