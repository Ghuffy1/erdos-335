import Erdos335.QuasiPeriodicRemainder
import Erdos335.LoebCriticalSolidity
import Erdos335.CompactDysonTransform

/-!
# An exclusive section in the strict Dyson argument

A sum outside the transformed set from an exclusive input coset fills
the remaining output measure. It gives a full-measure quasi-periodic
model of the original sum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance dysonExclusiveLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_dyson_exclusive_case_quasiPeriodic_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hIpos : 0 < loebMeasure U hU (A ∩ B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU ((A ∪ B) + (A ∩ B)) <
      loebMeasure U hU (A ∪ B) + loebMeasure U hU (A ∩ B))
    (a b : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (ha : a ∈ A) (hb : b ∈ B)
    (hexclusive : b ∉ A + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) ((A ∪ B) + (A ∩ B)) : Set _))
    (hout : a + b ∉ (A ∪ B) + (A ∩ B)) :
    let H := AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      ((A ∪ B) + (A ∩ B))
    ∃ D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      ∃ p : QuasiPeriodicDecomposition (loebMeasure U hU) H D,
        D ⊆ A + B ∧ (A + B =ᵐ[loebMeasure U hU] D) ∧
          p.background = (A ∪ B) + (A ∩ B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let T := (A ∪ B) + (A ∩ B)
  let H := AddAction.stabilizer G T
  let E := a +ᵥ (B ∩ (b +ᵥ (H : Set G)))
  let D := T ∪ E
  have hUpos : 0 < μ (A ∪ B) := hIpos.trans_le (measure_mono (inter_subset_left.trans subset_union_left))
  obtain ⟨hTm, hHm, _, hid⟩ := loeb_measurable_kneser_identity U hU q (A ∪ B) (A ∩ B)
    (hAm.union hBm) (hAm.inter hBm) hUpos hIpos hsmall
  have hperiod : T + (H : Set G) = T := by
    apply subset_antisymm
    · rintro x ⟨t, ht, k, hk, rfl⟩
      have hkT : k +ᵥ T = T := hk
      have hmem : k + t ∈ T := by rw [← hkT]; exact ⟨t, ht, rfl⟩
      simpa only [add_comm t k] using hmem
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hsection : (A ∪ B) ∩ (b +ᵥ (H : Set G)) = B ∩ (b +ᵥ (H : Set G)) := by
    apply subset_antisymm
    · rintro x ⟨hx, hxc⟩
      rcases hx with hxA | hxB
      · obtain ⟨k, hk, hkx⟩ := hxc
        apply False.elim
        apply hexclusive
        refine ⟨x, hxA, -k, H.neg_mem hk, ?_⟩
        change b + k = x at hkx
        rw [← hkx]
        abel
      · exact ⟨hxB, hxc⟩
    · exact inter_subset_inter_left _ subset_union_right
  have hbound : μ (A + B) ≤ μ T + μ (B ∩ (b +ᵥ (H : Set G))) := by
    have h := loeb_coset_section_bound_of_kneser_identity U hU H hHm (A ∪ B) (A ∩ B)
      hid b (Or.inr hb)
    rw [measure_union_add_inter A hBm, hsection, ← hfull] at h
    exact h
  have hEsub : E ⊆ A + B := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨a, ha, x, hx.1, rfl⟩
  have hEcoset : E ⊆ (a + b) +ᵥ (H : Set G) := by
    rintro z ⟨x, ⟨_, k, hk, hkx⟩, rfl⟩
    refine ⟨k, hk, ?_⟩
    change b + k = x at hkx
    change (a + b) + k = a + x
    rw [add_assoc, hkx]
  have hEs : MeasurableSet (B ∩ (b +ᵥ (H : Set G))) :=
    hBm.inter (measurable_loeb_coset U hU H hHm b)
  have hEm : MeasurableSet E := by
    dsimp only [E]
    rw [vadd_set_eq_neg_preimage]
    exact hEs.preimage (measurable_add_left U hU (-a))
  have hTsub : T ⊆ A + B := by
    rintro z ⟨u, (hu | hu), v, hv, rfl⟩
    · exact ⟨u, hu, v, hv.2, rfl⟩
    · exact ⟨v, hv.1, u, hu, add_comm _ _⟩
  have hDsub : D ⊆ A + B := union_subset hTsub hEsub
  have hd : Disjoint T E := (disjoint_periodic_set_coset H T hperiod _ hout).mono_right hEcoset
  have hDmass : μ (A + B) ≤ μ D := by
    change μ (A + B) ≤ μ (T ∪ E)
    rw [measure_union hd hEm, show μ E = μ (B ∩ (b +ᵥ (H : Set G))) from
      loebMeasure_image_add_left U hU a _]
    exact hbound
  have hDae : D =ᵐ[μ] A + B := ae_eq_of_subset_of_measure_ge hDsub hDmass
    (hTm.union hEm).nullMeasurableSet (measure_ne_top μ _)
  have hdiff : D \ T = E := by
    ext x
    constructor
    · rintro ⟨(hxT | hxE), hxout⟩
      · exact False.elim (hxout hxT)
      · exact hxE
    · intro hx
      exact ⟨Or.inr hx, fun hxT => Set.disjoint_left.mp hd hxT hx⟩
  have hne : (D \ T).Nonempty := by
    rw [hdiff]
    exact ⟨a + b, b, ⟨hb, 0, H.zero_mem, by simp⟩, rfl⟩
  obtain ⟨p, hpT, _, _⟩ := exists_quasiPeriodicDecomposition_of_single_coset_remainder
    μ H D T (a + b) (hTm.union hEm) hTm subset_union_left hperiod hout (hdiff ▸ hEcoset) hne
  exact ⟨D, p, hDsub, hDae.symm, hpT⟩

end Erdos335.Loeb

end
