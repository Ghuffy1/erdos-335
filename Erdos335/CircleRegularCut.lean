import Erdos335.IndicatorDerivativePoints
import Erdos335.ShiftedPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Regular complement points for cutting a measurable circle set
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory

namespace Erdos335.Loeb

theorem volume_unitCircle_lift_openInterval
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' S ∩ Ioo (0 : ℝ) 1) = volume S := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have heq : (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' S ∩ Ioo (0 : ℝ) 1) =ᵐ[volume]
      (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' S ∩ Ioc (0 : ℝ) 1) := by
    filter_upwards [Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := 0) (b := 1)] with x hx
    simp only [mem_inter_iff, hx]
  rw [measure_congr heq]
  simpa only [zero_add] using (AddCircle.add_projection_respects_measure (1 : ℝ) 0 hS).symm

theorem exists_unitCircle_regular_cut
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S) (hcomp : 0 < volume Sᶜ) :
    ∃ c ∈ Ioo (0 : ℝ) 1, (c : AddCircle (1 : ℝ)) ∉ S ∧
      HasDerivAt (fun y => ∫ (x : ℝ) in 0..y,
        S.indicator (fun _ => (1 : ℝ)) ((x + c : ℝ) : AddCircle (1 : ℝ))) 0 0 := by
  let E : Set ℝ := ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' S
  have hE : MeasurableSet E := hS.preimage AddCircle.measurable_mk'
  have hset : Ioo (0 : ℝ) 1 \ E =
      ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' Sᶜ ∩ Ioo (0 : ℝ) 1 := by
    ext x
    simp only [E, mem_diff, mem_Ioo, mem_preimage, mem_compl_iff, mem_inter_iff, and_comm]
  have hpositive : 0 < volume (Ioo (0 : ℝ) 1 \ E) := by
    rw [hset, volume_unitCircle_lift_openInterval Sᶜ hS.compl]
    exact hcomp
  obtain ⟨c, hc, hderiv⟩ := exists_zero_derivative_indicator_point E (Ioo 0 1) hE hpositive
  have hf : LocallyIntegrable (E.indicator (fun _ => (1 : ℝ))) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hE
  refine ⟨c, hc.1, hc.2, ?_⟩
  have hshift := shifted_primitive_derivative_zero _ hf c hderiv
  have hind (x : ℝ) : E.indicator (fun _ => (1 : ℝ)) x =
      S.indicator (fun _ => (1 : ℝ)) (x : AddCircle (1 : ℝ)) := by
    by_cases hx : (x : AddCircle (1 : ℝ)) ∈ S <;> simp [E, hx]
  simpa only [hind] using hshift

end Erdos335.Loeb
