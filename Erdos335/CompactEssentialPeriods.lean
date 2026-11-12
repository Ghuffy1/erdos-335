import Erdos335.HaarTranslation
import Mathlib.MeasureTheory.Group.AEStabilizer

/-!
# Closedness of the essential period subgroup

Translation acts continuously on the integral-norm space. Consequently the
almost-everywhere stabilizer of a measurable set is closed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

namespace Erdos335.Loeb

theorem isClosed_ae_function_periods
    {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup E]
    (μ : Measure G) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] (f : G → E) (hf : Integrable f μ) :
    IsClosed {a : G | (fun x => f (a + x)) =ᵐ[μ] f} := by
  let F : Lp E 1 μ := hf.toL1 f
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  letI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  have hrepr (a : G) : (((DomAddAct.mk a) +ᵥ F : Lp E 1 μ) : G → E) =ᵐ[μ]
      (fun x => f (a + x)) := by
    filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk a) F,
      (measurePreserving_add_left μ a).quasiMeasurePreserving.ae hf.coeFn_toL1] with x hx hfx
    change ((DomAddAct.mk a) +ᵥ F) x = F (a + x) at hx
    exact hx.trans hfx
  have heq (a : G) : ((DomAddAct.mk a) +ᵥ F = F) ↔ (fun x => f (a + x)) =ᵐ[μ] f := by
    constructor
    · intro h
      have hrep := hrepr a
      rw [h] at hrep
      exact hrep.symm.trans hf.coeFn_toL1
    · intro h
      exact Lp.ext ((hrepr a).trans (h.trans hf.coeFn_toL1.symm))
  have hc : Continuous (fun a : G => (DomAddAct.mk a) +ᵥ F) :=
    DomAddAct.continuous_mk.vadd continuous_const
  convert isClosed_eq hc (continuous_const (y := F)) using 1
  ext a
  exact (heq a).symm

theorem isClosed_aestabilizer
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] (A : Set G) (hA : MeasurableSet A) :
    IsClosed (AddAction.aestabilizer G μ A : Set G) := by
  classical
  let f := A.indicator (fun _ => (1 : ℝ))
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).indicator hA
  have hc := (isClosed_ae_function_periods μ f hfi).preimage (continuous_neg : Continuous (fun a : G => -a))
  convert hc using 1
  ext a
  change (a +ᵥ A =ᵐ[μ] A) ↔ (fun x => f (-a + x)) =ᵐ[μ] f
  apply eventually_congr
  filter_upwards with x
  have hmem : x ∈ a +ᵥ A ↔ -a + x ∈ A := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-a + x, hx, by simp⟩
  change ((x ∈ a +ᵥ A) = (x ∈ A)) ↔ f (-a + x) = f x
  by_cases hx : x ∈ A <;> by_cases ha : -a + x ∈ A <;> simp [hmem, f, hx, ha]

end Erdos335.Loeb
