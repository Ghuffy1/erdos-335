import Erdos335.LoebIrreducibleCore
import Erdos335.CompactDysonTransform

/-!
# Transferring one essential input period through an irreducible sum
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem MeasureIrreducible.sum_ae_period_of_left
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (inner : Set G → ℝ≥0∞) (hmono : Monotone inner)
    (heq : ∀ S : Set G, MeasurableSet S → inner S = μ S)
    (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hS : MeasurableSet (A + B)) (hirr : MeasureIrreducible μ inner A B)
    (t : G) (hperiod : t +ᵥ A =ᵐ[μ] A) : t +ᵥ (A + B) =ᵐ[μ] A + B := by
  let A₀ := A ∩ (t +ᵥ A)
  have htranslateA : MeasurableSet (t +ᵥ A) := by
    rw [vadd_set_eq_neg_preimage]
    exact hA.preimage (measurable_const_add (-t))
  have hA₀ : MeasurableSet A₀ := hA.inter htranslateA
  have hA₀ae : A₀ =ᵐ[μ] A := by
    filter_upwards [hperiod] with x hx
    simp only [A₀, mem_inter_iff, hx, and_self]
  have hinner : inner (A₀ + B) = μ (A + B) :=
    (hirr A₀ B hA₀ hB inter_subset_left Subset.rfl (measure_congr hA₀ae) rfl).trans
      (heq (A + B) hS)
  have htranslateS : MeasurableSet (t +ᵥ (A + B)) := by
    rw [vadd_set_eq_neg_preimage]
    exact hS.preimage (measurable_const_add (-t))
  have hsub : A₀ + B ⊆ (A + B) ∩ (t +ᵥ (A + B)) := by
    rintro z ⟨a, ha, b, hb, rfl⟩
    obtain ⟨a', ha', hea'⟩ := ha.2
    refine ⟨⟨a, ha.1, b, hb, rfl⟩, a' + b, ⟨a', ha', b, hb, rfl⟩, ?_⟩
    change t + (a' + b) = a + b
    change t + a' = a at hea'
    rw [← hea']
    abel
  have hbound : μ (A + B) ≤ μ ((A + B) ∩ (t +ᵥ (A + B))) := by
    calc
      μ (A + B) = inner (A₀ + B) := hinner.symm
      _ ≤ inner ((A + B) ∩ (t +ᵥ (A + B))) := hmono hsub
      _ = μ ((A + B) ∩ (t +ᵥ (A + B))) := heq _ (hS.inter htranslateS)
  have hfirst : (A + B) ∩ (t +ᵥ (A + B)) =ᵐ[μ] A + B :=
    ae_eq_of_subset_of_measure_ge inter_subset_left hbound
      (hS.inter htranslateS).nullMeasurableSet (measure_ne_top μ _)
  have hmass : μ (t +ᵥ (A + B)) = μ (A + B) := by
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have hsecond : (A + B) ∩ (t +ᵥ (A + B)) =ᵐ[μ] t +ᵥ (A + B) :=
    ae_eq_of_subset_of_measure_ge inter_subset_right (hmass.trans_le hbound)
      (hS.inter htranslateS).nullMeasurableSet (measure_ne_top μ _)
  exact hsecond.symm.trans hfirst

end Erdos335.Loeb
