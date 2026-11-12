import Erdos335.LoebResidueMaskProfiles

/-!
# Finite periodic masks transfer between the two common-start models
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance windowPeriodTransferLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_residue_mask_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (R : Finset (ZMod (h : ℕ)))
    (hS : S =ᵐ[loebMeasure U hU]
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _))
    (r : ZMod (h : ℕ)) :
    (loebMeasure U hU (S ∩
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r})).toReal =
      if r ∈ R then (1 : ℝ) / (h : ℕ) else 0 := by
  classical
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  have hinter : S ∩ φ ⁻¹' {r} =ᵐ[loebMeasure U hU] φ ⁻¹' ((R ∩ {r} : Finset _) : Set _) := by
    filter_upwards [hS] with x hx
    change (x ∈ S ∧ φ x = r) = (φ x ∈ R ∩ {r})
    rw [hx]
    simp only [φ, mem_preimage, Finset.mem_coe, Finset.mem_inter, Finset.mem_singleton]
  rw [measure_congr hinter]
  rw [loebMeasure_naturalCyclicProjection_preimage U hU q h hd (R ∩ {r})]
  by_cases hr : r ∈ R
  · have heq : R ∩ {r} = {r} := by ext x; simp; aesop
    simp [heq, hr]
  · have heq : R ∩ {r} = ∅ := by ext x; simp; aesop
    simp [heq, hr]

theorem loeb_window_residue_mask_transfer
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ℕ → Set ℕ) (start H : ℕ → ℕ) (p q : ℕ → ℕ+)
    (hH : ∀ s, 0 < H s) (hHp : ∀ s, H s ≤ (p s : ℕ)) (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hp : Tendsto (fun s => (((p s : ℕ) - H s : ℕ) : ℝ) / (p s : ℕ)) atTop (𝓝 0))
    (hq : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0))
    (h : ℕ+) (hdp : ∀ᶠ s in atTop, (h : ℕ) ∣ (p s : ℕ))
    (hdq : ∀ᶠ s in atTop, (h : ℕ) ∣ (q s : ℕ)) (R : Finset (ZMod (h : ℕ)))
    (hmask : internalSet U (fun s => (cyclicWindow (A s) (start s) (p s : ℕ) :
      Set (ZMod (p s : ℕ)))) =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun s => naturalCyclicProjection (p s) h)) ⁻¹' (R : Set _)) :
    internalSet U (fun s => (cyclicWindow (A s) (start s) (q s : ℕ) :
      Set (ZMod (q s : ℕ)))) =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun s => naturalCyclicProjection (q s) h)) ⁻¹' (R : Set _) := by
  apply loeb_ae_eq_residue_mask_of_profile U hU q h (hdq.filter_mono hU) _
    (measurable_internalSet U _) R
  intro r
  exact (loeb_window_residue_measure_agreement U hU A start H p q hH hHp hHq hp hq h hdp hdq r).symm.trans
    (loeb_residue_mask_profile U hU p h (hdp.filter_mono hU) _ R hmask r)

end Erdos335.Loeb

end
