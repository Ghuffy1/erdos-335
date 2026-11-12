import Erdos335.IrreducibleInputPeriod

/-!
# Sumset containers from almost-everywhere input containers
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem MeasureIrreducible.sum_ae_subset_of_ae_containers
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasure μ]
    (inner : Set G → ℝ≥0∞) (hmono : Monotone inner)
    (heq : ∀ S : Set G, MeasurableSet S → inner S = μ S)
    (A B I J K : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hS : MeasurableSet (A + B)) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hK : MeasurableSet K) (hirr : MeasureIrreducible μ inner A B)
    (hAI : A =ᵐ[μ] I) (hBJ : B =ᵐ[μ] J) (hIJ : I + J ⊆ K) :
    A + B ≤ᵐ[μ] K := by
  let A₀ := A ∩ I
  let B₀ := B ∩ J
  have hA₀ae : A₀ =ᵐ[μ] A := by
    filter_upwards [hAI] with x hx
    simp only [A₀, mem_inter_iff, hx, and_self]
  have hB₀ae : B₀ =ᵐ[μ] B := by
    filter_upwards [hBJ] with x hx
    simp only [B₀, mem_inter_iff, hx, and_self]
  have hinner : inner (A₀ + B₀) = μ (A + B) :=
    (hirr A₀ B₀ (hA.inter hI) (hB.inter hJ) inter_subset_left inter_subset_left
      (measure_congr hA₀ae) (measure_congr hB₀ae)).trans (heq (A + B) hS)
  have hsub : A₀ + B₀ ⊆ (A + B) ∩ K :=
    subset_inter (add_subset_add inter_subset_left inter_subset_left)
      ((add_subset_add inter_subset_right inter_subset_right).trans hIJ)
  have hbound : μ (A + B) ≤ μ ((A + B) ∩ K) := by
    calc
      μ (A + B) = inner (A₀ + B₀) := hinner.symm
      _ ≤ inner ((A + B) ∩ K) := hmono hsub
      _ = μ ((A + B) ∩ K) := heq _ (hS.inter hK)
  have hintersection : (A + B) ∩ K =ᵐ[μ] A + B :=
    ae_eq_of_subset_of_measure_ge inter_subset_left hbound
      (hS.inter hK).nullMeasurableSet (measure_ne_top μ _)
  filter_upwards [hintersection.symm] with x hx hmem
  exact (show x ∈ (A + B) ∩ K from hx ▸ hmem).2

end Erdos335.Loeb
