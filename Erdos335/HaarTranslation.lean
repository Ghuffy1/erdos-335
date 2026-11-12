import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
# Translation continuity in the integral norm

This is the local estimate used to construct common approximate identities
for the two measurable inputs of a compact sumset problem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

theorem continuous_integral_norm_add_sub
    {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E]
    (μ : Measure G) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] (f : G → E) (hf : Integrable f μ) :
    Continuous (fun a : G => ∫ x, ‖f (a + x) - f x‖ ∂μ) := by
  let F : Lp E 1 μ := hf.toL1 f
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  letI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  have hc : Continuous (fun a : G => ‖((DomAddAct.mk a) +ᵥ F) - F‖) := by
    exact ((DomAddAct.continuous_mk.vadd continuous_const).sub continuous_const).norm
  convert hc using 1
  funext a
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub ((DomAddAct.mk a) +ᵥ F) F,
    DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk a) F,
    hf.coeFn_toL1,
    (measurePreserving_add_left μ a).quasiMeasurePreserving.ae hf.coeFn_toL1] with x hsub hact hx hax
  simp only [Pi.sub_apply] at hsub
  change ((DomAddAct.mk a) +ᵥ F) x = F (a + x) at hact
  change F x = f x at hx
  change F (a + x) = f (a + x) at hax
  rw [hsub, hact, hx, hax]

theorem tendsto_integral_norm_add_sub_zero
    {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E]
    (μ : Measure G) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] (f : G → E) (hf : Integrable f μ) :
    Tendsto (fun a : G => ∫ x, ‖f (a + x) - f x‖ ∂μ) (𝓝 0) (𝓝 0) := by
  simpa using (continuous_integral_norm_add_sub μ f hf).tendsto 0

end Erdos335.Loeb
