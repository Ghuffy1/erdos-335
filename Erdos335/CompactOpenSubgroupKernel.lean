import Erdos335.SubgroupAEMeasure
import Erdos335.CompactFiniteCharacterKernel

/-!
# The finite-kernel criterion inside a connected open subgroup
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem finite_character_kernel_on_connected_open_subgroup
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (H : OpenAddSubgroup G) [ConnectedSpace H]
    (S : Set G) (hSm : MeasurableSet S) (hSH : S ⊆ H)
    (hperiod : ∀ t : G, t +ᵥ S =ᵐ[μ] S → t = 0)
    (A B : ℕ → Set G) (hAH : ∀ n, A n ⊆ H) (hBH : ∀ n, B n ⊆ H)
    (hBm : ∀ n, MeasurableSet (B n)) (hBpos : ∀ n, 0 < μ (B n))
    (hsum : ∀ n, A n + B n =ᵐ[μ] S)
    (hmass : ∀ n, μ S = μ (A n) + μ (B n))
    (hlocal : ∀ V ∈ 𝓝 (0 : G), ∀ᶠ n in atTop, B n - B n ⊆ V)
    (χ : H →+ AddCircle (1 : ℝ)) (hχ : Continuous χ) (hχne : χ ≠ 0) :
    Finite χ.ker := by
  have : IsTopologicalAddGroup H := inferInstanceAs (IsTopologicalAddGroup H.toAddSubgroup)
  have : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  have : MeasurableAdd₂ H := ⟨by
    exact ((measurable_subtype_coe.comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk⟩
  obtain ⟨ν, hνprob, hνhaar, hνimage⟩ := exists_normalized_open_subgroup_measure μ H
  have : IsProbabilityMeasure ν := hνprob
  have : ν.IsAddHaarMeasure := hνhaar
  let ι : H →+ G := H.toAddSubgroup.subtype
  let T : Set H := ι ⁻¹' S
  let P (n : ℕ) : Set H := ι ⁻¹' A n
  let Q (n : ℕ) : Set H := ι ⁻¹' B n
  have hι : Measurable ι := measurable_subtype_coe
  have hκpos : 0 < μ (H : Set G) := H.isOpen.measure_pos μ ⟨0, H.zero_mem⟩
  have hκreal : 0 < (μ (H : Set G)).toReal :=
    ENNReal.toReal_pos hκpos.ne' (measure_ne_top μ _)
  have hmeasure (E : Set G) (hE : E ⊆ H) : μ E = μ (H : Set G) * ν (ι ⁻¹' E) :=
    subgroup_measure_preimage H.toAddSubgroup μ ν (μ (H : Set G)) hνimage E hE
  have hTperiod (t : H) (ht : t +ᵥ T =ᵐ[ν] T) : t = 0 := by
    apply Subtype.ext
    apply hperiod
    exact (ae_period_subgroup_iff H.toAddSubgroup μ ν (μ (H : Set G)) hκpos.ne'
      hνimage S hSH t).mpr ht
  have hQpos (n : ℕ) : 0 < ν (Q n) := by
    by_contra h
    have hz : ν (Q n) = 0 := le_antisymm (not_lt.mp h) bot_le
    have hm := hmeasure (B n) (hBH n)
    change μ (B n) = μ (H : Set G) * ν (Q n) at hm
    rw [hz, mul_zero] at hm
    exact (hBpos n).ne' hm
  have hsumH (n : ℕ) : P n + Q n ≤ᵐ[ν] T := by
    have hsumH := (ae_eq_subgroup_iff H.toAddSubgroup μ ν (μ (H : Set G)) hκpos.ne'
      hνimage (A n + B n) S (fun x hx => by
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        exact H.add_mem (hAH n ha) (hBH n hb)) hSH).mp (hsum n)
    rw [subgroup_preimage_add H.toAddSubgroup (A n) (B n) (hAH n) (hBH n)] at hsumH
    exact hsumH.le
  have hmassH (n : ℕ) : (ν T).toReal = (ν (P n)).toReal + (ν (Q n)).toReal := by
    have hreal := congrArg ENNReal.toReal (hmass n)
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
      hmeasure S hSH, hmeasure (A n) (hAH n), hmeasure (B n) (hBH n)] at hreal
    simp only [ENNReal.toReal_mul] at hreal
    change (μ (H : Set G)).toReal * (ν T).toReal =
      (μ (H : Set G)).toReal * (ν (P n)).toReal +
      (μ (H : Set G)).toReal * (ν (Q n)).toReal at hreal
    nlinarith
  have hlocalH : ∀ V ∈ 𝓝 (0 : H), ∀ᶠ n in atTop, Q n - Q n ⊆ V := by
    intro V hV
    have hιEmbedding : Topology.IsEmbedding ι := Topology.IsEmbedding.subtypeVal
    have hind : 𝓝 (0 : H) = Filter.comap ι (𝓝 (0 : G)) := by
      simpa only [map_zero] using hιEmbedding.isInducing.nhds_eq_comap (0 : H)
    rw [hind] at hV
    obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
    filter_upwards [hlocal W hW] with n hn
    rintro z ⟨x, hx, y, hy, rfl⟩
    apply hWV
    exact hn ⟨ι x, hx, ι y, hy, (map_sub ι x y).symm⟩
  exact finite_character_kernel_of_localized_critical_pairs ν T (hSm.preimage hι) hTperiod
    χ hχ hχne P Q (fun n => (hBm n).preimage hι) hQpos hsumH hmassH hlocalH

end Erdos335.Loeb
