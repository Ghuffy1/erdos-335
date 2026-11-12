import Erdos335.LoebCrossEqualityEnvelope
import Erdos335.LoebEqualityCompletion
import Erdos335.LoebSparseDecomposition

/-!
# Reducible equality pairs with two equality cross sums

The common cross-sum envelope is exactly one coset larger than the
critical core. Its stabilizer and the saturated Kneser identity force
one null exceptional input coset on each side. Failure of essential
periodicity isolates their sum and gives its zero inner measure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance reducibleCrossEqualLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_reducible_cross_equal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU Acore) (hBpos : 0 < loebMeasure U hU Bcore)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hAmass : loebMeasure U hU A = loebMeasure U hU Acore)
    (hBmass : loebMeasure U hU B = loebMeasure U hU Bcore)
    (hcore : internalInnerMeasure U hU (Acore + Bcore) <
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hcrossleft : internalInnerMeasure U hU (A + Bcore) =
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hcrossright : internalInnerMeasure U hU (Acore + B) =
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hfull : internalInnerMeasure U hU (A + B) =
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hnotperiod : ¬ (A + B) + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (Acore + Bcore) : Set _) =ᵐ[loebMeasure U hU] A + B) :
    ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      loebMeasure U hU p.left.active = 0 ∧ loebMeasure U hU p.right.active = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let H := AddAction.stabilizer G (Acore + Bcore)
  let P := Acore + (H : Set G)
  let Q := Bcore + (H : Set G)
  let T := (A + Bcore) + (H : Set G)
  obtain ⟨_, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q Acore Bcore
    hAcorem hBcorem hApos hBpos hcore
  obtain ⟨hAperiod, hBperiod⟩ := loeb_reducible_equal_cross_core_periods U hU q Acore Bcore A B
    hAcorem hBcorem hApos hBpos hAsub hBsub hcore hcrossleft hcrossright
  obtain ⟨hXm, _, _, _⟩ := loeb_reducible_equal_cross_sum_periods U hU q Acore Bcore A B
    hAcorem hBcorem hApos hBpos hAsub hBsub hcore hcrossleft hcrossright
  have hCeq : Acore + Bcore = P + Q :=
    loeb_add_eq_add_saturations_of_essential_periods U hU H Acore Bcore
      hHm hHpos hAcorem hBcorem hAperiod hBperiod
  have hPperiod : P + (H : Set G) = P := by dsimp only [P]; rw [add_assoc, coe_add_coe]
  have hQperiod : Q + (H : Set G) = Q := by dsimp only [Q]; rw [add_assoc, coe_add_coe]
  have hTperiod : T + (H : Set G) = T := by dsimp only [T]; rw [add_assoc, coe_add_coe]
  have hPm : MeasurableSet P := measurable_saturation_of_positive_subgroup U hU q H hHm hHpos Acore
  have hQm : MeasurableSet Q := measurable_saturation_of_positive_subgroup U hU q H hHm hHpos Bcore
  have hPmass : μ P = μ Acore := loeb_measure_saturation_eq_of_essential_period U hU H Acore hAcorem hAperiod
  have hQmass : μ Q = μ Bcore := loeb_measure_saturation_eq_of_essential_period U hU H Bcore hBcorem hBperiod
  obtain ⟨hTsame, hTmass, g, hg, hTunion⟩ := loeb_cross_equality_periodic_envelope U hU q Acore Bcore A B
    hAcorem hBcorem hApos hBpos hAsub hBsub hcore hcrossleft hcrossright hfull
  have hAQ : A + Q = T := by dsimp only [Q, T]; rw [add_assoc]
  have hPB : P + B = T := by
    calc
      P + B = (Acore + B) + (H : Set G) := by dsimp only [P]; ac_rfl
      _ = T := hTsame.symm
  have hfullT : internalInnerMeasure U hU (A + B) = μ T := hfull.trans hTmass.symm
  have hAout : ¬ A ⊆ P := by
    intro hAP
    have hsub : A + B ⊆ T := by rw [← hPB]; exact add_subset_add hAP Subset.rfl
    exact hnotperiod (loeb_essential_period_of_full_inner_subset U hU q H (A + B) T hsub hfullT hTperiod)
  have hBout : ¬ B ⊆ Q := by
    intro hBQ
    have hsub : A + B ⊆ T := by rw [← hAQ]; exact add_subset_add Subset.rfl hBQ
    exact hnotperiod (loeb_essential_period_of_full_inner_subset U hU q H (A + B) T hsub hfullT hTperiod)
  have hH : AddAction.stabilizer G T = H :=
    loeb_stabilizer_of_single_coset_envelope U hU q H P Q A B T g hHm hHpos hPm hQm
      (by rwa [hPmass]) (by rwa [hQmass]) hTperiod (by rwa [← hCeq]) (by rwa [← hCeq])
      hAQ.subset hPB.subset (by rwa [hPmass, hQmass]) hfullT hnotperiod
  have hPsub : P ⊆ A + (H : Set G) := add_subset_add hAsub Subset.rfl
  have hQsub : Q ⊆ B + (H : Set G) := add_subset_add hBsub Subset.rfl
  obtain ⟨a, haout, hAsat⟩ := loeb_equality_completion_single_coset U hU q H P Q A T hHm hHpos
    hPm hQm (by rwa [hPmass]) (by rwa [hQmass]) hPperiod hQperiod hPsub hAQ hAout hH
    (by rwa [hPmass, hQmass])
  obtain ⟨b, hbout, hBsat⟩ := loeb_equality_completion_single_coset U hU q H Q P B T hHm hHpos
    hQm hPm (by rwa [hQmass]) (by rwa [hPmass]) hQperiod hPperiod hQsub
    (by simpa only [add_comm] using hPB) hBout hH (by rw [hQmass, hPmass, add_comm]; exact hTmass)
  have hAupper : A ⊆ P ∪ (a +ᵥ (H : Set G)) := by
    rw [← hAsat]
    exact fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hBupper : B ⊆ Q ∪ (b +ᵥ (H : Set G)) := by
    rw [← hBsat]
    exact fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  obtain ⟨xa, hxa, hxan⟩ := Set.not_subset.mp hAout
  obtain ⟨xb, hxb, hxbn⟩ := Set.not_subset.mp hBout
  obtain ⟨left, hleftactive, hleftbackground, hleftanchor, hleftzero⟩ :=
    exists_quasiPeriodicDecomposition_of_sparse_extension U hU q H Acore A a hHm hHpos
      hAcorem hAm hAsub hAmass hAperiod hAupper ⟨xa, hxa, hxan⟩
  obtain ⟨right, hrightactive, hrightbackground, hrightanchor, hrightzero⟩ :=
    exists_quasiPeriodicDecomposition_of_sparse_extension U hU q H Bcore B b hHm hHpos
      hBcorem hBm hBsub hBmass hBperiod hBupper ⟨xb, hxb, hxbn⟩
  have habout : a + b ∉ T := by
    intro hab
    have hsum : A + B ⊆ T := by
      rintro z ⟨x, hx, y, hy, rfl⟩
      rcases hAupper hx with hxP | hxcoset
      · rw [← hPB]
        exact add_mem_add hxP hy
      rcases hBupper hy with hyQ | hycoset
      · rw [← hAQ]
        exact add_mem_add hx hyQ
      obtain ⟨k, hk, rfl⟩ := hxcoset
      obtain ⟨l, hl, rfl⟩ := hycoset
      rw [← hTperiod]
      exact ⟨a + b, hab, k + l, H.add_mem hk hl, by simp only [vadd_eq_add]; abel⟩
    exact hnotperiod (loeb_essential_period_of_full_inner_subset U hU q H (A + B) T hsum hfullT hTperiod)
  have hcosetout : ∀ z ∈ (a + b) +ᵥ (H : Set G), z ∉ T := by
    rintro z ⟨k, hk, hkz⟩ hz
    apply habout
    have hback : z + -k ∈ T + (H : Set G) := add_mem_add hz (H.neg_mem hk)
    rw [hTperiod] at hback
    change a + b + k = z at hkz
    simpa only [← hkz, add_neg_cancel_right] using hback
  have hunique : ∀ x ∈ A, ∀ y ∈ B, x + y ∈ (a + b) +ᵥ (H : Set G) →
      x ∈ a +ᵥ (H : Set G) ∧ y ∈ b +ᵥ (H : Set G) := by
    intro x hx y hy hxy
    have hnotT := hcosetout (x + y) hxy
    constructor
    · exact (hAupper hx).resolve_left (fun hxP => hnotT (hPB ▸ add_mem_add hxP hy))
    · exact (hBupper hy).resolve_left (fun hyQ => hnotT (hAQ ▸ add_mem_add hx hyQ))
  have hXT : A + Bcore ⊆ T := fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hactiveSubset : left.active + right.active ⊆ (A + B) \ (A + Bcore) := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hxA : x ∈ A := (show x ∈ A \ P from hleftactive ▸ hx).1
    have hyB : y ∈ B := (show y ∈ B \ Q from hrightactive ▸ hy).1
    have hxcoset := left.active_subset_coset hx
    have hycoset := right.active_subset_coset hy
    rw [hleftanchor] at hxcoset
    rw [hrightanchor] at hycoset
    obtain ⟨k, hk, hkx⟩ := hxcoset
    obtain ⟨l, hl, hly⟩ := hycoset
    refine ⟨add_mem_add hxA hyB, fun hxy => hcosetout (x + y) ?_ (hXT hxy)⟩
    refine ⟨k + l, H.add_mem hk hl, ?_⟩
    change a + k = x at hkx
    change b + l = y at hly
    change (a + b) + (k + l) = x + y
    rw [← hkx, ← hly]
    abel
  have hXS : A + Bcore ⊆ A + B := add_subset_add Subset.rfl hBsub
  have hsplit := internalInnerMeasure_eq_add_sdiff U hU (A + B) (A + Bcore) hXm hXS
  have hfullX : internalInnerMeasure U hU (A + B) = μ (A + Bcore) := by
    rw [← internalInnerMeasure_eq U hU (A + Bcore) hXm]
    exact hfull.trans hcrossleft.symm
  have hactivezero : internalInnerMeasure U hU (left.active + right.active) = 0 := by
    apply le_antisymm
    · apply (ENNReal.add_le_add_iff_left (measure_ne_top μ (A + Bcore))).mp
      calc
        μ (A + Bcore) + internalInnerMeasure U hU (left.active + right.active) ≤
            μ (A + Bcore) + internalInnerMeasure U hU ((A + B) \ (A + Bcore)) :=
          add_le_add le_rfl (internalInnerMeasure_mono U hU hactiveSubset)
        _ = internalInnerMeasure U hU (A + B) := hsplit.symm
        _ = μ (A + Bcore) + 0 := by simpa only [add_zero] using hfullX
    · exact bot_le
  have hbackground : left.background.Nonempty := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hApos.ne'
    rw [hleftbackground]
    exact ⟨x, hAsub hx, x, hx, 0, H.zero_mem, add_zero x⟩
  let p : QuasiPeriodicPairData μ (internalInnerMeasure U hU) A B := {
    period := H
    period_measurable := hHm
    period_positive := hHpos
    left := left
    right := right
    nonempty_background := Or.inl hbackground
    unique_expression := by simpa only [hleftanchor, hrightanchor] using hunique
    active_identity := by rw [hleftzero, hrightzero, add_zero]; exact hactivezero
  }
  exact ⟨p, hleftzero, hrightzero⟩

end Erdos335.Loeb

end
