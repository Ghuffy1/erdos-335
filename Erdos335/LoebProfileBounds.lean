import Erdos335.LoebFiniteResidueProfiles

/-!
# Profile values from containment and almost-everywhere equality
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance profileBoundsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loebResidueProfile_eq_of_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (S T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hST : S =ᵐ[loebMeasure U hU] T) (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h S r = loebResidueProfile U hU q h T r := by
  have hinter : S ∩ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r} =ᵐ[loebMeasure U hU]
      T ∩ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r} := by
    filter_upwards [hST] with x hx
    change (x ∈ S ∧ _) = (x ∈ T ∧ _)
    rw [hx]
  unfold loebResidueProfile
  rw [measure_congr hinter]

theorem loebResidueProfile_zero_of_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (R : Finset (ZMod (h : ℕ)))
    (hS : S ⊆ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _))
    (r : ZMod (h : ℕ)) (hr : r ∉ R) : loebResidueProfile U hU q h S r = 0 := by
  have heq : S ∩ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hRx := hS hx.1
    have hxr : finiteQuotient U (fun n => naturalCyclicProjection (q n) h) x = r := hx.2
    exact hr (hxr ▸ hRx)
  unfold loebResidueProfile
  rw [heq, measure_empty, ENNReal.toReal_zero, mul_zero]

theorem loebResidueProfile_one_of_fiber_ae_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (r : ZMod (h : ℕ))
    (hS : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r} ≤ᵐ[loebMeasure U hU] S) :
    loebResidueProfile U hU q h S r = 1 := by
  have heq : S ∩ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r} =ᵐ[loebMeasure U hU]
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r} := by
    filter_upwards [hS] with x hx
    apply propext
    exact ⟨fun h => h.2, fun h => ⟨hx h, h⟩⟩
  unfold loebResidueProfile
  rw [measure_congr heq]
  have hm := loebMeasure_naturalCyclicProjection_preimage U hU q h hd ({r} : Finset (ZMod (h : ℕ)))
  simp only [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] at hm
  rw [hm, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  field_simp

end Erdos335.Loeb

end
