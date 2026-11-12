import Erdos335.LoebQuasiPeriodicAETransfer
import Erdos335.LoebDysonBackgrounds
import Erdos335.LoebTranslationStructure

/-!
# A quasi-periodic full-measure core in the complement

The complement of a quasi-periodic model has a full-measure
quasi-periodic core whenever its active coset is not full in measure.
Null changes in the original sum are removed by intersection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicComplementLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_complement_core
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hSm : MeasurableSet S)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H D)
    (hDS : D =ᵐ[loebMeasure U hU] S)
    (hpartial : loebMeasure U hU p.active < loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    ∃ C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      C ⊆ Sᶜ ∧ C =ᵐ[loebMeasure U hU] Sᶜ ∧
      ∃ r : QuasiPeriodicDecomposition (loebMeasure U hU) H C,
        0 < loebMeasure U hU r.active := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let K := p.anchor +ᵥ (H : Set G)
  let P := p.background + (H : Set G)
  let E := P ∪ p.active
  let R := (P ∪ K)ᶜ
  let Q := K \ p.active
  let active := Q ∩ Sᶜ
  let background := R ∩ Sᶜ
  let C := background ∪ active
  have hKm : MeasurableSet K := measurable_loeb_coset U hU H hHm p.anchor
  have hPm : MeasurableSet P := measurable_saturation_of_positive_subgroup U hU q H hHm hHpos p.background
  have hPH : P + (H : Set G) = P := by dsimp only [P]; rw [add_assoc, coe_add_coe]
  have hKH : K + (H : Set G) = K := by
    dsimp only [K]
    rw [vadd_set_add_eq, coe_add_coe]
  have hSat : p.active + (H : Set G) = K := by
    obtain ⟨a, ha⟩ := p.active_nonempty
    obtain ⟨ka, hka, hkaa⟩ := p.active_subset_coset ha
    apply subset_antisymm
    · rintro z ⟨x, hx, h, hh, rfl⟩
      obtain ⟨k, hk, hkx⟩ := p.active_subset_coset hx
      refine ⟨k + h, H.add_mem hk hh, ?_⟩
      change p.anchor + k = x at hkx
      change p.anchor + (k + h) = x + h
      rw [← add_assoc, hkx]
    · rintro z ⟨k, hk, hkz⟩
      refine ⟨a, ha, k - ka, H.sub_mem hk hka, ?_⟩
      change p.anchor + ka = a at hkaa
      change p.anchor + k = z at hkz
      change a + (k - ka) = z
      rw [← hkaa, ← hkz]
      abel
  have hKBg : Disjoint K p.background := hSat ▸ p.separated
  have hPK : Disjoint P K := by
    apply Set.disjoint_left.mpr
    rintro z ⟨b, hb, h, hh, rfl⟩ hzK
    have hbK : b ∈ K := by
      have hm : (b + h) + (-h) ∈ K + (H : Set G) := ⟨b + h, hzK, -h, H.neg_mem hh, rfl⟩
      rw [hKH] at hm
      simpa only [add_neg_cancel_right] using hm
    exact Set.disjoint_left.mp hKBg hbK hb
  have hBgP : p.background ⊆ P := fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hPae : P =ᵐ[μ] p.background :=
    (ae_le_set.mpr p.background_periodic).antisymm hBgP.eventuallySubset
  have hEae : E =ᵐ[μ] S := by
    apply Filter.EventuallyEq.trans _ hDS
    filter_upwards [hPae] with x hx
    change (x ∈ P ∨ x ∈ p.active) = (x ∈ D)
    rw [hx]
    exact (congrArg (fun T : Set G => x ∈ T) p.partition).symm
  have hRsub : R ⊆ Eᶜ := by
    rintro x hx (hxP | hxAct)
    · exact hx (Or.inl hxP)
    · exact hx (Or.inr (p.active_subset_coset hxAct))
  have hQsub : Q ⊆ Eᶜ := by
    rintro x ⟨hxK, hxAct⟩ (hxP | hxA)
    · exact Set.disjoint_left.mp hPK hxP hxK
    · exact hxAct hxA
  have hBgAE : background =ᵐ[μ] R := by
    filter_upwards [hEae] with x hx
    apply propext
    constructor
    · exact And.left
    · intro hxR
      exact ⟨hxR, fun hxS => hRsub hxR (hx.mpr hxS)⟩
  have hActAE : active =ᵐ[μ] Q := by
    filter_upwards [hEae] with x hx
    apply propext
    constructor
    · exact And.left
    · intro hxQ
      exact ⟨hxQ, fun hxS => hQsub hxQ (hx.mpr hxS)⟩
  have hCae : C =ᵐ[μ] Sᶜ := by
    filter_upwards [hEae] with x hx
    apply propext
    constructor
    · rintro (hxBg | hxAct)
      · exact hxBg.2
      · exact hxAct.2
    · intro hxS
      have hxE : x ∉ E := fun he => hxS (hx.mp he)
      by_cases hxK : x ∈ K
      · exact Or.inr ⟨⟨hxK, fun ha => hxE (Or.inr ha)⟩, hxS⟩
      · exact Or.inl ⟨fun he => he.elim (fun hp => hxE (Or.inl hp)) hxK, hxS⟩
  have hRm : MeasurableSet R := (hPm.union hKm).compl
  have hQm : MeasurableSet Q := hKm.diff p.active_measurable
  have hActm : MeasurableSet active := hQm.inter hSm.compl
  have hBgm : MeasurableSet background := hRm.inter hSm.compl
  have hQpos : 0 < μ Q := by
    rw [show μ Q = μ K - μ p.active from
      measure_sdiff p.active_subset_coset p.active_measurable.nullMeasurableSet (measure_ne_top μ _),
      show μ K = μ (H : Set G) from loebMeasure_coset U hU H p.anchor]
    exact tsub_pos_iff_lt.mpr hpartial
  have hActpos : 0 < μ active := (measure_congr hActAE).symm ▸ hQpos
  have hRH : R + (H : Set G) = R := complement_add_period H (P ∪ K) (by rw [union_add, hPH, hKH])
  have hBgperiod : μ ((background + (H : Set G)) \ background) = 0 := by
    apply essential_periodic_subset_of_null_difference μ H background R inter_subset_left
      (ae_le_set.mp hBgAE.ge)
    rw [hRH, Set.sdiff_self, measure_empty]
  let r : QuasiPeriodicDecomposition μ H C := {
    active := active
    background := background
    anchor := p.anchor
    active_measurable := hActm
    background_measurable := hBgm
    active_nonempty := nonempty_of_measure_ne_zero hActpos.ne'
    partition := rfl
    active_subset_coset := fun _ hx => hx.1.1
    separated := by
      apply Set.disjoint_left.mpr
      rintro x ⟨y, hy, h, hh, rfl⟩ hx
      have hm : y + h ∈ K + (H : Set G) := ⟨y, hy.1.1, h, hh, rfl⟩
      rw [hKH] at hm
      exact hx.1 (Or.inr hm)
    background_periodic := hBgperiod
  }
  exact ⟨C, union_subset inter_subset_right inter_subset_right, hCae, r, hActpos⟩

end Erdos335.Loeb

end
