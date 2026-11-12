import Erdos335.LoebCriticalExtensions
import Erdos335.LoebCriticalBackground

/-!
# One extra coset in an equality extension of a critical pair

This is the coset-counting step in Griesmer's Lemma 9.11. Two different
extra output cosets would each contribute the full critical deficit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

private theorem disjoint_cosets_of_sub_not_mem
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (a b : G) (hnot : a - b ∉ H) :
    Disjoint (a +ᵥ (H : Set G)) (b +ᵥ (H : Set G)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨k, hk, hek⟩ ⟨l, hl, hel⟩
  apply hnot
  have heq : a + k = b + l := hek.trans hel.symm
  have hdiff : a - b = l - k := by
    calc
      a - b = (a + k) - (b + k) := by abel
      _ = (b + l) - (b + k) := by rw [heq]
      _ = l - k := by abel
  rw [hdiff]
  exact H.sub_mem hl hk

private theorem disjoint_stabilizer_coset_of_not_mem
    {G : Type*} [AddCommGroup G] (C : Set G) (x : G) (hx : x ∉ C) :
    Disjoint C (x +ᵥ (AddAction.stabilizer G C : Set G)) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨k, hk, hkz⟩
  have hfix : (-k) +ᵥ C = C := (AddAction.stabilizer G C).neg_mem hk
  apply hx
  rw [← hfix]
  refine ⟨z, hz, ?_⟩
  change x + k = z at hkz
  change -k + z = x
  rw [← hkz]
  simp [add_comm]

private theorem translate_section_subset_coset
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (A : Set G) (a b : G) :
    b +ᵥ (A ∩ (a +ᵥ (H : Set G))) ⊆ (a + b) +ᵥ (H : Set G) := by
  rintro x ⟨y, ⟨_, ⟨k, hk, rfl⟩⟩, rfl⟩
  exact ⟨k, hk, by simp [vadd_eq_add]; abel⟩

local instance extraCosetLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

private theorem measurable_translate
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hA : MeasurableSet A)
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) : MeasurableSet (a +ᵥ A) := by
  have heq : a +ᵥ A = (fun x => -a + x) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, vadd_eq_add, neg_add_cancel_left] using hy
    · intro hx
      exact ⟨-a + x, hx, by simp [vadd_eq_add]⟩
  rw [heq]
  exact hA.preimage (measurable_add_left U hU (-a))

theorem loeb_equality_extension_extra_outputs_same_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B₀ B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hB₀m : MeasurableSet B₀)
    (hApos : 0 < loebMeasure U hU A) (hB₀pos : 0 < loebMeasure U hU B₀)
    (hB₀B : B₀ ⊆ B)
    (hcore : internalInnerMeasure U hU (A + B₀) < loebMeasure U hU A + loebMeasure U hU B₀)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B₀)
    (a₁ a₂ b₁ b₂ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hout₁ : a₁ + b₁ ∉ A + B₀) (hout₂ : a₂ + b₂ ∉ A + B₀) :
    (a₁ + b₁) - (a₂ + b₂) ∈
      AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (A + B₀) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let H := AddAction.stabilizer G (A + B₀)
  let C := A + B₀
  let D₁ := A ∩ (a₁ +ᵥ (H : Set G))
  let D₂ := A ∩ (a₂ +ᵥ (H : Set G))
  let E₁ := b₁ +ᵥ D₁
  let E₂ := b₂ +ᵥ D₂
  obtain ⟨hCm, hHm, _, hid⟩ := loeb_measurable_kneser_identity U hU q A B₀ hAm hB₀m hApos hB₀pos hcore
  have hD₁m : MeasurableSet D₁ := hAm.inter (measurable_loeb_coset U hU H hHm a₁)
  have hD₂m : MeasurableSet D₂ := hAm.inter (measurable_loeb_coset U hU H hHm a₂)
  have hE₁m : MeasurableSet E₁ := measurable_translate U hU q D₁ hD₁m b₁
  have hE₂m : MeasurableSet E₂ := measurable_translate U hU q D₂ hD₂m b₂
  by_contra hnot
  have hEC₁ := translate_section_subset_coset H A a₁ b₁
  have hEC₂ := translate_section_subset_coset H A a₂ b₂
  have hd₀₁ : Disjoint C E₁ := (disjoint_stabilizer_coset_of_not_mem C (a₁ + b₁) hout₁).mono_right hEC₁
  have hd₀₂ : Disjoint C E₂ := (disjoint_stabilizer_coset_of_not_mem C (a₂ + b₂) hout₂).mono_right hEC₂
  have hd₁₂ : Disjoint E₁ E₂ := (disjoint_cosets_of_sub_not_mem H (a₁ + b₁) (a₂ + b₂) hnot).mono hEC₁ hEC₂
  have hsub : (C ∪ E₁) ∪ E₂ ⊆ A + B := by
    rintro x ((hx | hx) | hx)
    · exact add_subset_add (show A ⊆ A from Subset.rfl) hB₀B hx
    · obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy.1, b₁, hb₁, add_comm y b₁⟩
    · obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy.1, b₂, hb₂, add_comm y b₂⟩
  have hmeasure : (μ C + μ D₁) + μ D₂ ≤ μ A + μ B₀ := by
    rw [← hequality]
    calc
      (μ C + μ D₁) + μ D₂ = (μ C + μ E₁) + μ E₂ := by
        rw [show μ E₁ = μ D₁ from loebMeasure_image_add_left U hU b₁ D₁,
          show μ E₂ = μ D₂ from loebMeasure_image_add_left U hU b₂ D₂]
      _ = μ ((C ∪ E₁) ∪ E₂) := by
        rw [measure_union (hd₀₂.union_left hd₁₂) hE₂m, measure_union hd₀₁ hE₁m]
      _ = internalInnerMeasure U hU ((C ∪ E₁) ∪ E₂) :=
        (internalInnerMeasure_eq U hU _ ((hCm.union hE₁m).union hE₂m)).symm
      _ ≤ internalInnerMeasure U hU (A + B) := internalInnerMeasure_mono U hU hsub
  have hbound₁ := loeb_coset_section_bound_of_kneser_identity U hU H hHm A B₀ hid a₁ ha₁
  have hbound₂ := loeb_coset_section_bound_of_kneser_identity U hU H hHm A B₀ hid a₂ ha₂
  have hmeasureR := ENNReal.toReal_mono (by finiteness) hmeasure
  rw [ENNReal.toReal_add (by finiteness) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hmeasureR
  have hbound₁R := ENNReal.toReal_mono (by finiteness) hbound₁
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hbound₁R
  have hbound₂R := ENNReal.toReal_mono (by finiteness) hbound₂
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hbound₂R
  have hstrict : μ C < μ A + μ B₀ := by
    rwa [internalInnerMeasure_eq U hU (A + B₀) hCm] at hcore
  have hstrictR := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by finiteness)).mpr hstrict
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hstrictR
  change (μ A).toReal + (μ B₀).toReal ≤ (μ C).toReal + (μ D₁).toReal at hbound₁R
  change (μ A).toReal + (μ B₀).toReal ≤ (μ C).toReal + (μ D₂).toReal at hbound₂R
  linarith

theorem loeb_equality_extension_extra_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B₀ B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hB₀m : MeasurableSet B₀)
    (hApos : 0 < loebMeasure U hU A) (hB₀pos : 0 < loebMeasure U hU B₀)
    (hB₀B : B₀ ⊆ B)
    (hcore : internalInnerMeasure U hU (A + B₀) < loebMeasure U hU A + loebMeasure U hU B₀)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B₀) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + B₀)
    ∃ g ∈ (A + B) \ (A + B₀), ((A + B) + (H : Set G)) \ (A + B₀) = g +ᵥ (H : Set G) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let H := AddAction.stabilizer G (A + B₀)
  have hnotSub : ¬A + B ⊆ A + B₀ := by
    intro hsub
    have hle := internalInnerMeasure_mono U hU hsub
    rw [hequality] at hle
    exact (not_le_of_gt hcore) hle
  obtain ⟨g, hg, hgout⟩ := Set.not_subset.mp hnotSub
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  refine ⟨a + b, ⟨⟨a, ha, b, hb, rfl⟩, hgout⟩, ?_⟩
  apply subset_antisymm
  · rintro z ⟨⟨y, ⟨a', ha', b', hb', rfl⟩, k, hk, heq⟩, hzout⟩
    have hyout : a' + b' ∉ A + B₀ := by
      intro hy
      apply hzout
      have hfix : k +ᵥ (A + B₀) = A + B₀ := hk
      rw [← hfix]
      refine ⟨a' + b', hy, ?_⟩
      change (a' + b') + k = z at heq
      change k + (a' + b') = z
      rw [add_comm k, heq]
    have hdiff := loeb_equality_extension_extra_outputs_same_coset U hU q A B₀ B
      hAm hB₀m hApos hB₀pos hB₀B hcore hequality a' a b' b ha' ha hb' hb hyout hgout
    refine ⟨((a' + b') - (a + b)) + k, H.add_mem hdiff hk, ?_⟩
    change (a' + b') + k = z at heq
    change (a + b) + (((a' + b') - (a + b)) + k) = z
    calc
      _ = (a' + b') + k := by abel
      _ = z := heq
  · rintro z ⟨k, hk, rfl⟩
    refine ⟨⟨a + b, ⟨a, ha, b, hb, rfl⟩, k, hk, rfl⟩, ?_⟩
    intro hz
    have hfix : (-k) +ᵥ (A + B₀) = A + B₀ := H.neg_mem hk
    apply hgout
    rw [← hfix]
    exact ⟨(a + b) + k, hz, by simp only [vadd_eq_add]; abel⟩

theorem loeb_equality_extension_periodic_backgrounds
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B₀ B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hB₀m : MeasurableSet B₀)
    (hApos : 0 < loebMeasure U hU A) (hB₀pos : 0 < loebMeasure U hU B₀)
    (hB₀B : B₀ ⊆ B)
    (hcore : internalInnerMeasure U hU (A + B₀) < loebMeasure U hU A + loebMeasure U hU B₀)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B₀) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + B₀)
    ∃ a ∈ A, ∃ b ∈ B, a + b ∉ A + B₀ ∧
      loebMeasure U hU A + loebMeasure U hU B₀ =
        loebMeasure U hU (A + B₀) + loebMeasure U hU (A ∩ (a +ᵥ (H : Set G))) ∧
      loebMeasure U hU ((B₀ + (H : Set G)) \ B₀) = 0 ∧
      loebMeasure U hU (((A \ (a +ᵥ (H : Set G))) + (H : Set G)) \ (A \ (a +ᵥ (H : Set G)))) = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let H := AddAction.stabilizer G (A + B₀)
  obtain ⟨hCm, hHm, _, hid⟩ := loeb_measurable_kneser_identity U hU q A B₀ hAm hB₀m hApos hB₀pos hcore
  obtain ⟨g, hg, _⟩ := loeb_equality_extension_extra_coset U hU q A B₀ B
    hAm hB₀m hApos hB₀pos hB₀B hcore hequality
  obtain ⟨a, ha, b, hb, rfl⟩ := hg.1
  have hout : a + b ∉ A + B₀ := hg.2
  let D := A ∩ (a +ᵥ (H : Set G))
  let E := b +ᵥ D
  have hDm : MeasurableSet D := hAm.inter (measurable_loeb_coset U hU H hHm a)
  have hEm : MeasurableSet E := measurable_translate U hU q D hDm b
  have hdisj : Disjoint (A + B₀) E :=
    (disjoint_stabilizer_coset_of_not_mem (A + B₀) (a + b) hout).mono_right
      (translate_section_subset_coset H A a b)
  have hsub : (A + B₀) ∪ E ⊆ A + B := by
    rintro x (hx | hx)
    · exact add_subset_add (show A ⊆ A from Subset.rfl) hB₀B hx
    · obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy.1, b, hb, add_comm y b⟩
  have hupper : μ (A + B₀) + μ D ≤ internalInnerMeasure U hU (A + B) := by
    calc
      μ (A + B₀) + μ D = μ (A + B₀) + μ E := by
        rw [show μ E = μ D from loebMeasure_image_add_left U hU b D]
      _ = μ ((A + B₀) ∪ E) := (measure_union hdisj hEm).symm
      _ = internalInnerMeasure U hU ((A + B₀) ∪ E) :=
        (internalInnerMeasure_eq U hU _ (hCm.union hEm)).symm
      _ ≤ internalInnerMeasure U hU (A + B) := internalInnerMeasure_mono U hU hsub
  have hlower := loeb_coset_section_bound_of_kneser_identity U hU H hHm A B₀ hid a ha
  have hactive : μ A + μ B₀ = μ (A + B₀) + μ D :=
    le_antisymm hlower (hupper.trans_eq hequality)
  obtain ⟨hBperiod, hAperiod⟩ := loeb_critical_background_periodic U hU H hHm A B₀ hAm hB₀m a ha hid hactive
  exact ⟨a, ha, b, hb, hout, hactive, hBperiod, hAperiod⟩

end Erdos335.Loeb

end
