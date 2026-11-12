import Erdos335.LoebCriticalMaximality

/-!
# Extensions of a strict critical pair

If enlarging both inputs keeps the inner measure of their sum below the
original total input measure, the sum and its occupied quotient classes
remain the same. Positive mass in each occupied coset forces this result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance criticalExtensionsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_critical_extension_left_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hsmall : internalInnerMeasure U hU (A' + B') < loebMeasure U hU A + loebMeasure U hU B) :
    A' ⊆ A + (AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      (A + B) : Set _) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let H := AddAction.stabilizer G (A + B)
  have hcore : internalInnerMeasure U hU (A + B) < μ A + μ B :=
    (internalInnerMeasure_mono U hU (add_subset_add hAA' hBB')).trans_lt hsmall
  obtain ⟨hCm, hHm, _, hid⟩ := loeb_measurable_kneser_identity U hU q A B hAm hBm hApos hBpos hcore
  intro a ha
  by_contra hout
  have hex : ∃ b ∈ B, a + b ∉ A + B := by
    by_contra hn
    have hsub : a +ᵥ B ⊆ A + B := by
      rintro x ⟨b, hb, rfl⟩
      by_contra hx
      exact hn ⟨b, hb, hx⟩
    have hzero : μ ((a +ᵥ B) \ (A + B)) = 0 := by
      rw [sdiff_eq_empty.mpr hsub, measure_empty]
    exact hout (loeb_critical_translate_maximal U hU q A B hAm hBm hApos hBpos hcore a hzero)
  obtain ⟨b, hb, hab⟩ := hex
  let D := B ∩ (b +ᵥ (H : Set G))
  let E := (fun x => a + x) '' D
  have hDm : MeasurableSet D := hBm.inter (measurable_loeb_coset U hU H hHm b)
  have hEm : MeasurableSet E := by
    have heq : E = (fun x => -a + x) ⁻¹' D := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa only [mem_preimage, neg_add_cancel_left] using hy
      · intro hx
        exact ⟨-a + x, hx, by simp⟩
    rw [heq]
    exact hDm.preimage (measurable_add_left U hU (-a))
  have hdisj : Disjoint (A + B) E := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨y, ⟨hyB, ⟨k, hk, rfl⟩⟩, rfl⟩
    have hfix : (-k) +ᵥ (A + B) = A + B := H.neg_mem hk
    apply hab
    rw [← hfix]
    exact ⟨a + (b + k), hx, by simp [vadd_eq_add]; abel⟩
  have hsub : (A + B) ∪ E ⊆ A' + B' := by
    rintro x (hx | hx)
    · exact add_subset_add hAA' hBB' hx
    · obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨a, ha, y, hBB' hy.1, rfl⟩
  have hmass : μ (A + B) + μ D ≤ internalInnerMeasure U hU (A' + B') := by
    calc
      μ (A + B) + μ D = μ (A + B) + μ E := by
        rw [show μ E = μ D from loebMeasure_image_add_left U hU a D]
      _ = μ ((A + B) ∪ E) := (measure_union hdisj hEm).symm
      _ = internalInnerMeasure U hU ((A + B) ∪ E) :=
        (internalInnerMeasure_eq U hU _ (hCm.union hEm)).symm
      _ ≤ internalInnerMeasure U hU (A' + B') := internalInnerMeasure_mono U hU hsub
  have hid' : μ (B + (H : Set G)) + μ (A + (H : Set G)) = μ (B + A) + μ (H : Set G) := by
    rw [add_comm B A, add_comm (μ (B + (H : Set G))) (μ (A + (H : Set G)))]
    exact hid
  have hbound := loeb_coset_section_bound_of_kneser_identity U hU H hHm B A hid' b hb
  have hbound' : μ A + μ B ≤ μ (A + B) + μ D := by
    simpa only [add_comm] using hbound
  exact (not_lt_of_ge (hbound'.trans hmass)) hsmall

theorem loeb_critical_extensions_eq
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hsmall : internalInnerMeasure U hU (A' + B') < loebMeasure U hU A + loebMeasure U hU B) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + B)
    A' + B' = A + B ∧
      A' + (H : Set G) = A + (H : Set G) ∧ B' + (H : Set G) = B + (H : Set G) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let H := AddAction.stabilizer G (A + B)
  have hleft := loeb_critical_extension_left_subset U hU q A B A' B'
    hAm hBm hApos hBpos hAA' hBB' hsmall
  have hsmall' : internalInnerMeasure U hU (B' + A') < loebMeasure U hU B + loebMeasure U hU A := by
    simpa only [add_comm] using hsmall
  have hright := loeb_critical_extension_left_subset U hU q B A B' A'
    hBm hAm hBpos hApos hBB' hAA' hsmall'
  rw [add_comm B A] at hright
  have hsum : A' + B' = A + B := by
    apply subset_antisymm
    · rintro x ⟨a', ha', b', hb', rfl⟩
      obtain ⟨a, ha, k, hk, hka⟩ := hleft ha'
      obtain ⟨b, hb, l, hl, hlb⟩ := hright hb'
      have hfix : (k + l) +ᵥ (A + B) = A + B := H.add_mem hk hl
      rw [← hfix]
      refine ⟨a + b, add_mem_add ha hb, ?_⟩
      change (k + l) + (a + b) = a' + b'
      change a + k = a' at hka
      change b + l = b' at hlb
      rw [← hka, ← hlb]
      abel
    · exact add_subset_add hAA' hBB'
  have hAsat : A' + (H : Set G) = A + (H : Set G) := by
    apply subset_antisymm
    · rintro x ⟨a', ha', k, hk, rfl⟩
      obtain ⟨a, ha, l, hl, hla⟩ := hleft ha'
      refine ⟨a, ha, l + k, H.add_mem hl hk, ?_⟩
      change a + l = a' at hla
      rw [← hla]
      abel
    · exact add_subset_add hAA' (show (H : Set G) ⊆ H from Subset.rfl)
  have hBsat : B' + (H : Set G) = B + (H : Set G) := by
    apply subset_antisymm
    · rintro x ⟨b', hb', k, hk, rfl⟩
      obtain ⟨b, hb, l, hl, hlb⟩ := hright hb'
      refine ⟨b, hb, l + k, H.add_mem hl hk, ?_⟩
      change b + l = b' at hlb
      rw [← hlb]
      abel
    · exact add_subset_add hBB' (show (H : Set G) ⊆ H from Subset.rfl)
  exact ⟨hsum, hAsat, hBsat⟩

theorem loeb_critical_null_extensions_sum_eq
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hAmass : loebMeasure U hU A' = loebMeasure U hU A)
    (hBmass : loebMeasure U hU B' = loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (A' + B') < loebMeasure U hU A' + loebMeasure U hU B') :
    A' + B' = A + B := by
  rw [hAmass, hBmass] at hsmall
  exact (loeb_critical_extensions_eq U hU q A B A' B' hAm hBm hApos hBpos hAA' hBB' hsmall).1

end Erdos335.Loeb

end
