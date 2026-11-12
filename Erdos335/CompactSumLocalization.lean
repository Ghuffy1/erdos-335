import Erdos335.CompactOverlap

/-!
# Localization of shrinking summands in a compact aperiodic sumset

This is the localization claim in Griesmer's Proposition 6.2. The overlap
bound uses literal translations of the smaller summand and almost-everywhere
containment of its sumset in the fixed set.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]

theorem haarOverlap_ge_of_sumset_ae_subset
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (A B S : Set G) (hsum : A + B ≤ᵐ[μ] S)
    (x y : G) (hx : x ∈ B) (hy : y ∈ B) :
    (μ A).toReal ≤ haarOverlap μ S (x - y) := by
  have hshift := (measurePreserving_add_left μ (y - x)).quasiMeasurePreserving.ae hsum
  have hsub : x +ᵥ A ≤ᵐ[μ] S ∩ ((x - y) +ᵥ S) := by
    filter_upwards [hsum, hshift] with z hz hzshift
    rintro ⟨a, ha, rfl⟩
    have hfirst : x + a ∈ S := hz ⟨a, ha, x, hx, by ac_rfl⟩
    have hsecond : (y - x) + (x + a) ∈ S :=
      hzshift ⟨a, ha, y, hy, by change a + y = (y - x) + (x + a); abel⟩
    exact ⟨hfirst, (y - x) + (x + a), hsecond, by change (x - y) + ((y - x) + (x + a)) = x + a; abel⟩
  have hmass : μ (x +ᵥ A) = μ A := by
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have hle := measure_mono_ae hsub
  rw [hmass] at hle
  exact ENNReal.toReal_mono (measure_ne_top μ _) hle

theorem shrinking_sumsets_localize
    [CompactSpace G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (S : Set G) (hS : MeasurableSet S)
    (hperiod : ∀ z : G, z +ᵥ S =ᵐ[μ] S → z = 0)
    (A B : ℕ → Set G)
    (hsum : ∀ n, A n + B n ≤ᵐ[μ] S)
    (hmass : Tendsto (fun n => (μ (A n)).toReal) atTop (𝓝 (μ S).toReal))
    (U : Set G) (hU : U ∈ 𝓝 (0 : G)) :
    ∀ᶠ n in atTop, B n - B n ⊆ U := by
  apply eventually_difference_subset_of_unique_maximum (haarOverlap μ S)
    (continuous_haarOverlap μ S hS) (haarOverlap_strict_maximum μ S hS hperiod)
    (fun n => (μ (A n)).toReal) _ B _ U hU
  · simpa only [haarOverlap, zero_vadd, inter_self] using hmass
  · intro n x hx y hy
    exact haarOverlap_ge_of_sumset_ae_subset μ (A n) (B n) S (hsum n) x y hx hy

end Erdos335.Loeb

end
