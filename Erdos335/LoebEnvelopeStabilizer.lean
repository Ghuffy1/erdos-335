import Erdos335.LoebPeriodicCoreFoundations
import Erdos335.LoebPeriodicEquality

/-!
# The stabilizer of a one-coset cross-sum envelope

A larger stabilizer would make the saturated original inputs a strict
critical pair. Maximality would then put the entire original sum inside
the envelope, contradicting failure of essential periodicity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem subgroup_le_stabilizer_of_add_eq
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (T : Set G)
    (hperiod : T + (H : Set G) = T) : H ≤ AddAction.stabilizer G T := by
  intro k hk
  change k +ᵥ T = T
  apply subset_antisymm
  · rintro x ⟨t, ht, rfl⟩
    rw [← hperiod]
    exact ⟨t, ht, k, hk, add_comm t k⟩
  · intro x hx
    have hback : x + -k ∈ T + (H : Set G) := add_mem_add hx (H.neg_mem hk)
    rw [hperiod] at hback
    exact ⟨x + -k, hback, by simp [vadd_eq_add, add_comm, add_left_comm]⟩

theorem single_coset_extension_add_larger_subgroup
    {G : Type*} [AddCommGroup G] (H K : AddSubgroup G) (C T : Set G) (g : G)
    (hT : T = C ∪ (g +ᵥ (H : Set G))) (hperiod : T + (K : Set G) = T)
    (hextra : ∃ k ∈ K, k ∉ H) : C + (K : Set G) = T := by
  obtain ⟨k, hk, hkout⟩ := hextra
  have hCT : C ⊆ T := by rw [hT]; exact subset_union_left
  apply subset_antisymm
  · intro x hx
    rw [← hperiod]
    exact add_subset_add hCT Subset.rfl hx
  · intro x hx
    rcases hT ▸ hx with hxC | hxcoset
    · exact ⟨x, hxC, 0, K.zero_mem, add_zero x⟩
    obtain ⟨h, hh, hhx⟩ := hxcoset
    have hnext : x + k ∈ T := by
      rw [← hperiod]
      exact add_mem_add hx hk
    have hnextC : x + k ∈ C := by
      rcases hT ▸ hnext with hC | hcoset
      · exact hC
      obtain ⟨l, hl, hlx⟩ := hcoset
      apply False.elim
      apply hkout
      have heq : k = l - h := by
        change g + h = x at hhx
        change g + l = x + k at hlx
        rw [← hhx] at hlx
        have heq' : l = h + k := add_left_cancel (by simpa only [add_assoc] using hlx)
        rw [heq']
        abel
      rw [heq]
      exact H.sub_mem hl hh
    exact ⟨x + k, hnextC, -k, K.neg_mem hk, by simp⟩

local instance envelopeStabilizerLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_stabilizer_of_single_coset_envelope
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (P Q A B T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (g : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hPm : MeasurableSet P) (hQm : MeasurableSet Q)
    (hPpos : 0 < loebMeasure U hU P) (hQpos : 0 < loebMeasure U hU Q)
    (hTperiod : T + (H : Set _) = T)
    (hT : T = (P + Q) ∪ (g +ᵥ (H : Set _))) (hg : g ∉ P + Q)
    (hA : A + Q ⊆ T) (hB : P + B ⊆ T)
    (hTmass : loebMeasure U hU T = loebMeasure U hU P + loebMeasure U hU Q)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU T)
    (hnotperiod : ¬ (A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B) :
    AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) T = H := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let K := AddAction.stabilizer G T
  have hHK : H ≤ K := subgroup_le_stabilizer_of_add_eq H T hTperiod
  apply le_antisymm ?_ hHK
  by_contra hnot
  obtain ⟨k, hk, hkout⟩ := SetLike.not_le_iff_exists.mp hnot
  have hKperiod : T + (K : Set G) = T := by
    apply subset_antisymm
    · rintro x ⟨t, ht, l, hl, rfl⟩
      have hfix : l +ᵥ T = T := hl
      rw [← hfix]
      exact ⟨t, ht, add_comm l t⟩
    · intro x hx
      exact ⟨x, hx, 0, K.zero_mem, add_zero x⟩
  have hKH : (K : Set G) + (H : Set G) = K := by
    apply subset_antisymm
    · rintro x ⟨l, hl, h, hh, rfl⟩
      exact K.add_mem hl (hHK hh)
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hKm : MeasurableSet (K : Set G) := by
    rw [← hKH]
    exact measurable_saturation_of_positive_subgroup U hU q H hHm hHpos K
  have hKpos : 0 < μ (K : Set G) := hHpos.trans_le (measure_mono hHK)
  have hfill : (P + Q) + (K : Set G) = T :=
    single_coset_extension_add_larger_subgroup H K (P + Q) T g hT hKperiod ⟨k, hk, hkout⟩
  have hTm : MeasurableSet T := by
    rw [← hTperiod]
    exact measurable_saturation_of_positive_subgroup U hU q H hHm hHpos T
  have hlarge : μ P + μ Q < μ (P + (K : Set G)) + μ (Q + (K : Set G)) := by
    by_contra hn
    have hle := le_of_not_gt hn
    have hdeficit : μ (P + (K : Set G)) + μ (Q + (K : Set G)) < μ P + μ Q + μ (K : Set G) :=
      hle.trans_lt (ENNReal.lt_add_right (by finiteness) hKpos.ne')
    have hstable := loeb_add_periodic_of_saturated_deficit U hU K hKm P Q hQm hdeficit
    have hgelem : g ∈ T := by rw [hT]; exact Or.inr ⟨0, H.zero_mem, by simp⟩
    rw [← hfill, hstable] at hgelem
    exact hg hgelem
  let PK := P + (K : Set G)
  let QK := Q + (K : Set G)
  have hPKm : MeasurableSet PK := measurable_saturation_of_positive_subgroup U hU q K hKm hKpos P
  have hQKm : MeasurableSet QK := measurable_saturation_of_positive_subgroup U hU q K hKm hKpos Q
  have hPsub : P ⊆ PK := fun x hx => ⟨x, hx, 0, K.zero_mem, add_zero x⟩
  have hQsub : Q ⊆ QK := fun x hx => ⟨x, hx, 0, K.zero_mem, add_zero x⟩
  have hPKperiod : PK + (K : Set G) = PK := by dsimp only [PK]; rw [add_assoc, coe_add_coe]
  have hQKperiod : QK + (K : Set G) = QK := by dsimp only [QK]; rw [add_assoc, coe_add_coe]
  have hsum : PK + QK = T := by
    dsimp only [PK, QK]
    rw [add_add_add_comm, coe_add_coe, hfill]
  have hsmall : internalInnerMeasure U hU (PK + QK) < μ PK + μ QK := by
    rw [hsum, internalInnerMeasure_eq U hU T hTm, hTmass]
    exact hlarge
  have hAin : A ⊆ PK := by
    intro a ha
    have hsub : a +ᵥ QK ⊆ PK + QK := by
      rintro z ⟨y, ⟨b, hb, l, hl, hly⟩, rfl⟩
      rw [hsum, ← hKperiod]
      refine ⟨a + b, hA (add_mem_add ha hb), l, hl, ?_⟩
      change b + l = y at hly
      simp only [vadd_eq_add]
      rw [← hly]
      abel
    have hzero : μ ((a +ᵥ QK) \ (PK + QK)) = 0 := by rw [sdiff_eq_empty.mpr hsub, measure_empty]
    have h := loeb_critical_translate_maximal U hU q PK QK hPKm hQKm
      (hPpos.trans_le (measure_mono hPsub)) (hQpos.trans_le (measure_mono hQsub)) hsmall a hzero
    rw [hsum] at h
    change a ∈ PK + (K : Set G) at h
    rwa [hPKperiod] at h
  have hBin : B ⊆ QK := by
    intro b hb
    have hsub : b +ᵥ PK ⊆ QK + PK := by
      rintro z ⟨y, ⟨a, ha, l, hl, hly⟩, rfl⟩
      rw [add_comm QK PK, hsum, ← hKperiod]
      refine ⟨a + b, hB (add_mem_add ha hb), l, hl, ?_⟩
      change a + l = y at hly
      simp only [vadd_eq_add]
      rw [← hly]
      abel
    have hzero : μ ((b +ᵥ PK) \ (QK + PK)) = 0 := by rw [sdiff_eq_empty.mpr hsub, measure_empty]
    have h := loeb_critical_translate_maximal U hU q QK PK hQKm hPKm
      (hQpos.trans_le (measure_mono hQsub)) (hPpos.trans_le (measure_mono hPsub))
      (by simpa only [add_comm] using hsmall) b hzero
    rw [add_comm QK PK, hsum] at h
    change b ∈ QK + (K : Set G) at h
    rwa [hQKperiod] at h
  have hwhole : A + B ⊆ T := by rw [← hsum]; exact add_subset_add hAin hBin
  exact hnotperiod (loeb_essential_period_of_full_inner_subset U hU q H (A + B) T hwhole hfull hTperiod)

end Erdos335.Loeb

end
