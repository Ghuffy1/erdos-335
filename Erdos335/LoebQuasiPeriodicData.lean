import Erdos335.LoebOneSidedEquality

/-!
# Quasi-periodic pair data for the inverse theorem

The data retain exact partitions and literal coset separation, together
with the measure identities needed when an exceptional pair is refined.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

structure QuasiPeriodicDecomposition {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (H : AddSubgroup G) (A : Set G) where
  active : Set G
  background : Set G
  anchor : G
  active_measurable : MeasurableSet active
  background_measurable : MeasurableSet background
  active_nonempty : active.Nonempty
  partition : A = background ∪ active
  active_subset_coset : active ⊆ anchor +ᵥ (H : Set G)
  separated : Disjoint (active + (H : Set G)) background
  background_periodic : μ ((background + (H : Set G)) \ background) = 0

structure QuasiPeriodicPairData {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (inner : Set G → ℝ≥0∞) (A B : Set G) where
  period : AddSubgroup G
  period_measurable : MeasurableSet (period : Set G)
  period_positive : 0 < μ (period : Set G)
  left : QuasiPeriodicDecomposition μ period A
  right : QuasiPeriodicDecomposition μ period B
  nonempty_background : left.background.Nonempty ∨ right.background.Nonempty
  unique_expression : ∀ x ∈ A, ∀ y ∈ B,
    x + y ∈ (left.anchor + right.anchor) +ᵥ (period : Set G) →
      x ∈ left.anchor +ᵥ (period : Set G) ∧ y ∈ right.anchor +ᵥ (period : Set G)
  active_identity : inner (left.active + right.active) = μ left.active + μ right.active

def QuasiPeriodicPairData.swap
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    {μ : Measure G} {inner : Set G → ℝ≥0∞} {A B : Set G}
    (p : QuasiPeriodicPairData μ inner A B) : QuasiPeriodicPairData μ inner B A where
  period := p.period
  period_measurable := p.period_measurable
  period_positive := p.period_positive
  left := p.right
  right := p.left
  nonempty_background := p.nonempty_background.symm
  unique_expression := by
    intro x hx y hy hxy
    have h := p.unique_expression y hy x hx (by simpa only [add_comm] using hxy)
    exact h.symm
  active_identity := by
    rw [add_comm p.right.active p.left.active, add_comm (μ p.right.active) (μ p.left.active)]
    exact p.active_identity

local instance quasiDataLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_quasiPeriodicPairData_of_one_sided_equality
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A Bcore B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBcorem : MeasurableSet Bcore) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU Bcore)
    (hBsub : Bcore ⊆ B) (hBmass : loebMeasure U hU B = loebMeasure U hU Bcore)
    (hcore : internalInnerMeasure U hU (A + Bcore) < loebMeasure U hU A + loebMeasure U hU Bcore)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU Bcore)
    (hnotperiod : ¬ (A + B) + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (A + Bcore) : Set _) =ᵐ[loebMeasure U hU] A + B) :
    ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      loebMeasure U hU p.right.active = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let H := AddAction.stabilizer G (A + Bcore)
  obtain ⟨_, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q A Bcore
    hAm hBcorem hApos hBpos hcore
  obtain ⟨a, ha, b, hb, hA₀m, hA₁m, hB₀m, hB₁m, hA₀pos, _, hB₀zero,
      hB₀ne, hAeq, hBeq, hA₀sub, hB₀sub, hAdisjoint, hBdisjoint,
      hAperiod, hBperiod, hunique, hidentity⟩ :=
    loeb_one_sided_equality_reduction U hU q A Bcore B hAm hBcorem hBm
      hApos hBpos hBsub hBmass hcore hequality hnotperiod
  let left : QuasiPeriodicDecomposition μ H A := {
    active := A ∩ (a +ᵥ (H : Set G))
    background := A \ (a +ᵥ (H : Set G))
    anchor := a
    active_measurable := hA₀m
    background_measurable := hA₁m
    active_nonempty := nonempty_of_measure_ne_zero hA₀pos.ne'
    partition := hAeq
    active_subset_coset := hA₀sub
    separated := hAdisjoint
    background_periodic := hAperiod
  }
  let right : QuasiPeriodicDecomposition μ H B := {
    active := B \ (Bcore + (H : Set G))
    background := B ∩ (Bcore + (H : Set G))
    anchor := b
    active_measurable := hB₀m
    background_measurable := hB₁m
    active_nonempty := hB₀ne
    partition := hBeq
    active_subset_coset := hB₀sub
    separated := hBdisjoint
    background_periodic := hBperiod
  }
  have hBbackground : right.background.Nonempty := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hBpos.ne'
    exact ⟨x, hBsub hx, ⟨x, hx, 0, H.zero_mem, add_zero x⟩⟩
  let p : QuasiPeriodicPairData μ (internalInnerMeasure U hU) A B := {
    period := H
    period_measurable := hHm
    period_positive := hHpos
    left := left
    right := right
    nonempty_background := Or.inr hBbackground
    unique_expression := hunique
    active_identity := hidentity
  }
  exact ⟨p, hB₀zero⟩

end Erdos335.Loeb

end
