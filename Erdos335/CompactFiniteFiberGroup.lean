import Erdos335.CompactFiberMeasureBound
import Erdos335.CompactNullSingletons

/-!
# A finite fiber group forced by localized sets and controlled containers
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem finite_fiber_group_of_localized_containers
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [TopologicalSpace H] [T2Space G] [T2Space H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    [MeasurableAdd₂ G] [MeasurableAdd₂ H]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (ν : Measure H) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.InnerRegularCompactLTTop]
    (φ : H →+ G) (hφ : Topology.IsEmbedding φ)
    (B T : ℕ → Set G) (hBm : ∀ n, MeasurableSet (B n)) (hTm : ∀ n, MeasurableSet (T n))
    (hBT : ∀ n, B n ⊆ T n) (hperiod : ∀ n h, φ h +ᵥ T n = T n)
    (hBpos : ∀ n, 0 < μ (B n))
    (hlocal : ∀ V ∈ 𝓝 (0 : G), ∀ᶠ n in atTop, B n - B n ⊆ V)
    (C : ℝ) (hC : 0 < C) (hmass : ∀ n, (μ (T n)).toReal ≤ C * (μ (B n)).toReal) :
    Finite H := by
  by_contra hfinite
  have : Infinite H := not_finite_iff_infinite.mp hfinite
  obtain ⟨U, hUopen, hUzero, hUsmall⟩ := exists_small_open_identity_neighborhood ν (1 / C)
    (one_div_pos.mpr hC)
  have hUnear : U ∈ 𝓝 (0 : H) := hUopen.mem_nhds hUzero
  have hind : 𝓝 (0 : H) = Filter.comap φ (𝓝 (0 : G)) := by
    simpa only [map_zero] using hφ.isInducing.nhds_eq_comap (0 : H)
  rw [hind] at hUnear
  obtain ⟨V, hVnear, hVU⟩ := Filter.mem_comap.mp hUnear
  obtain ⟨n, hn⟩ := (hlocal V hVnear).exists
  have hδ : (ν (φ ⁻¹' V)).toReal ≤ (ν U).toReal :=
    ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hVU)
  have hproduct : C * (ν (φ ⁻¹' V)).toReal < 1 := by
    have hlt := hδ.trans_lt hUsmall
    have h := (lt_div_iff₀ hC).mp hlt
    simpa only [mul_comm] using h
  have hbound := measure_le_invariant_container_mul_fiber_diameter μ ν φ hφ.continuous.measurable
    (B n) (T n) V (hBm n) (hTm n) (hBT n) (hperiod n) hn
  have hpositive : 0 < (μ (B n)).toReal :=
    ENNReal.toReal_pos (hBpos n).ne' (measure_ne_top μ _)
  have hfinal : (μ (B n)).toReal ≤ (μ (B n)).toReal * (C * (ν (φ ⁻¹' V)).toReal) := by
    calc
      (μ (B n)).toReal ≤ (μ (T n)).toReal * (ν (φ ⁻¹' V)).toReal := hbound
      _ ≤ (C * (μ (B n)).toReal) * (ν (φ ⁻¹' V)).toReal :=
        mul_le_mul_of_nonneg_right (hmass n) ENNReal.toReal_nonneg
      _ = (μ (B n)).toReal * (C * (ν (φ ⁻¹' V)).toReal) := by ring
  have hstrict : (μ (B n)).toReal * (C * (ν (φ ⁻¹' V)).toReal) < (μ (B n)).toReal := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hproduct hpositive
  exact (not_lt_of_ge hfinal) hstrict

end Erdos335.Loeb
