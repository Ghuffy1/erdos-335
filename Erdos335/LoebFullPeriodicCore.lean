import Erdos335.LoebPeriodicCoreFoundations
import Erdos335.LoebSparseDecomposition

/-!
# Lifting a fully periodic equality core

The original pair differs from a full-measure periodic core by null
sets. If its sum fails essential periodicity, both exceptional inputs
lie in single cosets and form a quasi-periodic pair of inner sum zero.
This is the fully periodic input case of Griesmer's Lemma 10.12.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance fullPeriodicCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_full_periodic_core_reduction
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU Acore) (hBpos : 0 < loebMeasure U hU Bcore)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hAmass : loebMeasure U hU A = loebMeasure U hU Acore)
    (hBmass : loebMeasure U hU B = loebMeasure U hU Bcore)
    (hAperiod : loebMeasure U hU ((Acore + (H : Set _)) \ Acore) = 0)
    (hBperiod : loebMeasure U hU ((Bcore + (H : Set _)) \ Bcore) = 0)
    (hcore : loebMeasure U hU (Acore + Bcore) = loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU (Acore + Bcore))
    (hH : H = AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (Acore + Bcore))
    (hnotperiod : ¬ (A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B) :
    ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      loebMeasure U hU p.left.active = 0 ∧ loebMeasure U hU p.right.active = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let P := Acore + (H : Set G)
  let Q := Bcore + (H : Set G)
  let C := Acore + Bcore
  have hPperiod : P + (H : Set G) = P := by
    dsimp only [P]
    rw [add_assoc, coe_add_coe]
  have hQperiod : Q + (H : Set G) = Q := by
    dsimp only [Q]
    rw [add_assoc, coe_add_coe]
  have hCeq : C = P + Q :=
    loeb_add_eq_add_saturations_of_essential_periods U hU H Acore Bcore
      hHm hHpos hAcorem hBcorem hAperiod hBperiod
  have hCperiod : C + (H : Set G) = C := by rw [hCeq, add_assoc, hQperiod]
  have hPm : MeasurableSet P :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos Acore
  have hQm : MeasurableSet Q :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos Bcore
  have hCm : MeasurableSet C := by
    rw [← hCperiod]
    exact measurable_saturation_of_positive_subgroup U hU q H hHm hHpos C
  have hPmass : μ P = μ Acore :=
    loeb_measure_saturation_eq_of_essential_period U hU H Acore hAcorem hAperiod
  have hQmass : μ Q = μ Bcore :=
    loeb_measure_saturation_eq_of_essential_period U hU H Bcore hBcorem hBperiod
  have hPQm : MeasurableSet (P + Q) := hCeq ▸ hCm
  have hPQbound : μ (P + Q) ≤ μ P + μ Q := by rw [← hCeq, hPmass, hQmass]; exact hcore.le
  have hH' : H = AddAction.stabilizer G (P + Q) := by
    change H = AddAction.stabilizer G C at hH
    rwa [hCeq] at hH
  obtain ⟨hleft, hright⟩ := loeb_periodic_core_extensions_absorbed U hU q H Acore Bcore A B
    hHm hHpos hAcorem hBcorem hAsub hBsub hAperiod hBperiod hfull
  have hAout : ¬ A ⊆ P := by
    intro hAP
    have hsum : A + B ⊆ C := (add_subset_add hAP (show B ⊆ B from Subset.rfl)).trans hright
    exact hnotperiod (loeb_essential_period_of_full_inner_subset U hU q H (A + B) C hsum hfull hCperiod)
  have hBout : ¬ B ⊆ Q := by
    intro hBQ
    have hsum : A + B ⊆ C := (add_subset_add (show A ⊆ A from Subset.rfl) hBQ).trans hleft
    exact hnotperiod (loeb_essential_period_of_full_inner_subset U hU q H (A + B) C hsum hfull hCperiod)
  have hAcompletion := loeb_periodic_completion_one_coset U hU q H P Q A hPm hQm hPQm
    (by rwa [hPmass]) (by rwa [hQmass]) hPQbound hHm hHpos hH' hPperiod (by rwa [← hCeq])
  obtain ⟨a, haout, hAupper⟩ := hAcompletion.resolve_left hAout
  have hHswap : H = AddAction.stabilizer G (Q + P) := by simpa only [add_comm] using hH'
  have hBcompletion := loeb_periodic_completion_one_coset U hU q H Q P B hQm hPm
    (by simpa only [add_comm] using hPQm) (by rwa [hQmass]) (by rwa [hPmass])
    (by simpa only [add_comm] using hPQbound) hHm hHpos hHswap hQperiod (by
      simpa only [add_comm, ← hCeq] using hright)
  obtain ⟨b, hbout, hBupper⟩ := hBcompletion.resolve_left hBout
  obtain ⟨xa, hxaA, hxaP⟩ := Set.not_subset.mp hAout
  obtain ⟨xb, hxbB, hxbQ⟩ := Set.not_subset.mp hBout
  obtain ⟨left, hleftactive, hleftbackground, hleftanchor, hleftzero⟩ :=
    exists_quasiPeriodicDecomposition_of_sparse_extension U hU q H Acore A a hHm hHpos
      hAcorem hAm hAsub hAmass hAperiod hAupper ⟨xa, hxaA, hxaP⟩
  obtain ⟨right, hrightactive, hrightbackground, hrightanchor, hrightzero⟩ :=
    exists_quasiPeriodicDecomposition_of_sparse_extension U hU q H Bcore B b hHm hHpos
      hBcorem hBm hBsub hBmass hBperiod hBupper ⟨xb, hxbB, hxbQ⟩
  have habout : a + b ∉ C := by
    intro hab
    have hsum : A + B ⊆ C := by
      rintro z ⟨x, hx, y, hy, rfl⟩
      rcases hAupper hx with hxP | hxcoset
      · exact hright (add_mem_add hxP hy)
      rcases hBupper hy with hyQ | hycoset
      · exact hleft (add_mem_add hx hyQ)
      obtain ⟨k, hk, rfl⟩ := hxcoset
      obtain ⟨l, hl, rfl⟩ := hycoset
      rw [← hCperiod]
      exact ⟨a + b, hab, k + l, H.add_mem hk hl, by simp only [vadd_eq_add]; abel⟩
    exact hnotperiod (loeb_essential_period_of_full_inner_subset U hU q H (A + B) C hsum hfull hCperiod)
  have hcosetout : ∀ z ∈ (a + b) +ᵥ (H : Set G), z ∉ C := by
    rintro z ⟨k, hk, hkz⟩ hz
    apply habout
    have hback : z + -k ∈ C + (H : Set G) := add_mem_add hz (H.neg_mem hk)
    rw [hCperiod] at hback
    change a + b + k = z at hkz
    simpa only [← hkz, add_neg_cancel_right] using hback
  have hunique : ∀ x ∈ A, ∀ y ∈ B, x + y ∈ (a + b) +ᵥ (H : Set G) →
      x ∈ a +ᵥ (H : Set G) ∧ y ∈ b +ᵥ (H : Set G) := by
    intro x hx y hy hxy
    have hnotC := hcosetout (x + y) hxy
    constructor
    · exact (hAupper hx).resolve_left (fun hxP => hnotC (hright (add_mem_add hxP hy)))
    · exact (hBupper hy).resolve_left (fun hyQ => hnotC (hleft (add_mem_add hx hyQ)))
  have hactiveSubset : left.active + right.active ⊆ (A + B) \ C := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hxA : x ∈ A := (show x ∈ A \ P from hleftactive ▸ hx).1
    have hyB : y ∈ B := (show y ∈ B \ Q from hrightactive ▸ hy).1
    have hxcoset := left.active_subset_coset hx
    have hycoset := right.active_subset_coset hy
    rw [hleftanchor] at hxcoset
    rw [hrightanchor] at hycoset
    obtain ⟨k, hk, hkx⟩ := hxcoset
    obtain ⟨l, hl, hly⟩ := hycoset
    refine ⟨add_mem_add hxA hyB, hcosetout (x + y) ?_⟩
    refine ⟨k + l, H.add_mem hk hl, ?_⟩
    change a + k = x at hkx
    change b + l = y at hly
    change (a + b) + (k + l) = x + y
    rw [← hkx, ← hly]
    abel
  have hCS : C ⊆ A + B := add_subset_add hAsub hBsub
  have hsplit := internalInnerMeasure_eq_add_sdiff U hU (A + B) C hCm hCS
  have hactivezero : internalInnerMeasure U hU (left.active + right.active) = 0 := by
    apply le_antisymm
    · apply (ENNReal.add_le_add_iff_left (measure_ne_top μ C)).mp
      calc
        μ C + internalInnerMeasure U hU (left.active + right.active) ≤
            μ C + internalInnerMeasure U hU ((A + B) \ C) :=
          add_le_add le_rfl (internalInnerMeasure_mono U hU hactiveSubset)
        _ = internalInnerMeasure U hU (A + B) := hsplit.symm
        _ = μ C + 0 := by simpa only [add_zero] using hfull
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
