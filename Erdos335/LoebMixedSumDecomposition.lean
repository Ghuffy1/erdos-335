import Erdos335.LoebFiniteNoncriticalComponent
import Erdos335.LoebSingleOutsideCoset
import Erdos335.QuasiPeriodicRemainder

/-!
# Quasi-periodic output in the mixed-coset case

A finite coset cover provides a noncritical component outside the periodic
base. The per-coset deficit bounds then confine the whole remainder to its
one output coset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance mixedSumDecompositionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_mixed_sum_quasiPeriodic_decomposition
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (A B S T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hSm : MeasurableSet S) (hTm : MeasurableSet T)
    (hsplit : S = T ∪ (A + B)) (hperiod : T + (H : Set _) = T)
    (hsame : A + (H : Set _) = B + (H : Set _))
    (hstrict : loebMeasure U hU T < loebMeasure U hU S)
    (hbound : ∀ a ∈ A, loebMeasure U hU S ≤ loebMeasure U hU T +
      (loebMeasure U hU (A ∩ (a +ᵥ (H : Set _))) +
        loebMeasure U hU (B ∩ (a +ᵥ (H : Set _)))))
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      S + (L : Set _) = S) :
    ∃ p : QuasiPeriodicDecomposition (loebMeasure U hU) H S,
      p.background = T ∧ p.active = S \ T := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  obtain ⟨R, hRA, hRcover⟩ := loeb_exists_finite_coset_cover U hU q H hHm hHpos A
  let J := {rs : R × R // (rs.1 : G) + (rs.2 : G) ∉ T}
  let C (u : J) : Set G := A ∩ ((u.val.1 : G) +ᵥ (H : Set G))
  let D (u : J) : Set G := B ∩ ((u.val.2 : G) +ᵥ (H : Set G))
  have hC (u : J) : MeasurableSet (C u) := hAm.inter (measurable_loeb_coset U hU H hHm _)
  have hD (u : J) : MeasurableSet (D u) := hBm.inter (measurable_loeb_coset U hU H hHm _)
  have hCne (u : J) : (C u).Nonempty :=
    ⟨u.val.1, hRA u.val.1.property, 0, H.zero_mem, by simp⟩
  have hDne (u : J) : (D u).Nonempty :=
    coset_section_nonempty_of_saturation_eq H A B hsame u.val.2 (hRA u.val.2.property)
  have hdecomp : S = T ∪ ⋃ u : J, C u + D u := by
    ext z
    constructor
    · intro hz
      by_cases hzT : z ∈ T
      · exact Or.inl hzT
      obtain ⟨a, ha, b, hb, hab⟩ := (hsplit ▸ hz).resolve_left hzT
      have haR : a ∈ (R : Set G) + (H : Set G) := by
        rw [← hRcover]
        exact ⟨a, ha, 0, H.zero_mem, add_zero a⟩
      have hbR : b ∈ (R : Set G) + (H : Set G) := by
        rw [← hRcover, hsame]
        exact ⟨b, hb, 0, H.zero_mem, add_zero b⟩
      obtain ⟨i, hi, k, hk, hki⟩ := haR
      obtain ⟨j, hj, l, hl, hlj⟩ := hbR
      have hout : i + j ∉ T := by
        intro hij
        apply hzT
        have hmem : z ∈ T + (H : Set G) := by
          refine ⟨i + j, hij, k + l, H.add_mem hk hl, ?_⟩
          change i + k = a at hki
          change j + l = b at hlj
          calc
            (i + j) + (k + l) = (i + k) + (j + l) := by abel
            _ = z := by rw [hki, hlj]; exact hab
        rwa [hperiod] at hmem
      let u : J := ⟨(⟨i, hi⟩, ⟨j, hj⟩), hout⟩
      apply Or.inr
      apply mem_iUnion.mpr
      exact ⟨u, a, ⟨ha, k, hk, hki⟩, b, ⟨hb, l, hl, hlj⟩, hab⟩
    · rintro (hzT | hz)
      · rw [hsplit]
        exact Or.inl hzT
      · obtain ⟨u, a, ha, b, hb, hab⟩ := mem_iUnion.mp hz
        rw [hsplit]
        exact Or.inr ⟨a, ha.1, b, hb.1, hab⟩
  have hnotperiod' : ¬ ∃ L : AddSubgroup G, MeasurableSet (L : Set G) ∧
      0 < μ (L : Set G) ∧ (T ∪ ⋃ u : J, C u + D u) + (L : Set G) = T ∪ ⋃ u : J, C u + D u := by
    intro h
    apply hnotperiod
    rwa [← hdecomp] at h
  obtain ⟨u, hu⟩ := loeb_nonperiodic_union_base_has_noncritical_component U hU q C D
    hC hD hCne hDne T H hHm hHpos hperiod hnotperiod'
  have hsingle : S \ T ⊆ ((u.val.1 : G) + (u.val.2 : G)) +ᵥ (H : Set G) :=
    loeb_single_outside_coset_of_noncritical_section U hU H hHm A B S T hSm hsplit hperiod
      hsame hstrict hbound u.val.1 u.val.2 (hRA u.val.1.property) (hRA u.val.2.property) u.property hu
  have hne : (S \ T).Nonempty := by
    by_contra h
    have hST : S ⊆ T := sdiff_eq_empty.mp (not_nonempty_iff_eq_empty.mp h)
    exact (not_le_of_gt hstrict) (measure_mono hST)
  have hTS : T ⊆ S := by rw [hsplit]; exact subset_union_left
  obtain ⟨p, hpT, hpA, _⟩ := exists_quasiPeriodicDecomposition_of_single_coset_remainder
    μ H S T ((u.val.1 : G) + (u.val.2 : G)) hSm hTm hTS hperiod u.property hsingle hne
  exact ⟨p, hpT, hpA⟩

end Erdos335.Loeb

end
