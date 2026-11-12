import Erdos335.LoebQuasiPeriodicBackground
import Erdos335.LoebIrreducibleCore
import Erdos335.LoebInnerSplit

/-!
# Irreducibility of the active pair

Replacing each active input by a full-measure subset preserves the
measure of the whole input. The unchanged periodic background bounds
the whole replacement sum, so irreducibility of the original pair
forces equality for the active replacement sum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicIrreducibleLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_active_irreducible
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B) :
    MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) p.left.active p.right.active := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let T := (p.left.background + B) ∪ (A + p.right.background)
  let R := p.left.active + p.right.active
  have hTm : MeasurableSet T := (loeb_quasiPeriodic_background U hU q A B (internalInnerMeasure U hU) p).1
  have hsplit : A + B = T ∪ R := p.sum_partition
  have hTsub : T ⊆ A + B := subset_union_left.trans hsplit.ge
  have hRcoset : R ⊆ (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    obtain ⟨k, hk, hkx⟩ := p.left.active_subset_coset hx
    obtain ⟨l, hl, hly⟩ := p.right.active_subset_coset hy
    refine ⟨k + l, p.period.add_mem hk hl, ?_⟩
    change p.left.anchor + k = x at hkx
    change p.right.anchor + l = y at hly
    change (p.left.anchor + p.right.anchor) + (k + l) = x + y
    rw [← hkx, ← hly]
    ac_rfl
  have hTR : Disjoint T R := p.background_disjoint_active_coset.mono_right hRcoset
  have difference (X : Set G) (hXR : X ⊆ R) : (T ∪ X) \ T = X := by
    ext x
    constructor
    · rintro ⟨hxT | hxX, hn⟩
      · exact False.elim (hn hxT)
      · exact hxX
    · intro hxX
      exact ⟨Or.inr hxX, fun hxT => Set.disjoint_left.mp hTR hxT (hXR hxX)⟩
  have hwhole : internalInnerMeasure U hU (A + B) = μ T + internalInnerMeasure U hU R := by
    rw [internalInnerMeasure_eq_add_sdiff U hU (A + B) T hTm hTsub]
    have hdiff : (A + B) \ T = R := hsplit ▸ difference R Subset.rfl
    rw [hdiff]
  have mass_replacement {S : Set G} (d : QuasiPeriodicDecomposition μ p.period S)
      (P : Set G) (hPm : MeasurableSet P) (hPsub : P ⊆ d.active) (hPmass : μ P = μ d.active) :
      μ (d.background ∪ P) = μ S := by
    have hparts : Disjoint d.background d.active := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp d.separated ⟨x, hy, 0, p.period.zero_mem, add_zero x⟩ hx
    calc
      μ (d.background ∪ P) = μ d.background + μ P := measure_union (hparts.mono_right hPsub) hPm
      _ = μ d.background + μ d.active := by rw [hPmass]
      _ = μ S := ((congrArg μ d.partition).trans (measure_union hparts d.active_measurable)).symm
  intro P Q hPm hQm hPL hQR hPmass hQmass
  let A' := p.left.background ∪ P
  let B' := p.right.background ∪ Q
  have hA'm : MeasurableSet A' := p.left.background_measurable.union hPm
  have hB'm : MeasurableSet B' := p.right.background_measurable.union hQm
  have hA'A : A' ⊆ A := by
    intro x hx
    change x ∈ p.left.background ∨ x ∈ P at hx
    apply p.left.partition.ge
    exact hx.imp id (fun hy => hPL hy)
  have hB'B : B' ⊆ B := by
    intro x hx
    change x ∈ p.right.background ∨ x ∈ Q at hx
    apply p.right.partition.ge
    exact hx.imp id (fun hy => hQR hy)
  have hA'mass : μ A' = μ A := mass_replacement p.left P hPm hPL hPmass
  have hB'mass : μ B' = μ B := mass_replacement p.right Q hQm hQR hQmass
  have hsame : internalInnerMeasure U hU (A' + B') = internalInnerMeasure U hU (A + B) :=
    hirr A' B' hA'm hB'm hA'A hB'B hA'mass hB'mass
  have hPQsub : P + Q ⊆ R := add_subset_add hPL hQR
  have hnewsub : A' + B' ⊆ T ∪ (P + Q) := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    rcases hx with hxBg | hxP
    · exact Or.inl (Or.inl ⟨x, hxBg, y, hB'B hy, rfl⟩)
    · rcases hy with hyBg | hyQ
      · exact Or.inl (Or.inr ⟨x, hA'A (Or.inr hxP), y, hyBg, rfl⟩)
      · exact Or.inr ⟨x, hxP, y, hyQ, rfl⟩
  have hupper : internalInnerMeasure U hU (A + B) ≤ μ T + internalInnerMeasure U hU (P + Q) := by
    rw [← hsame]
    calc
      internalInnerMeasure U hU (A' + B') ≤ internalInnerMeasure U hU (T ∪ (P + Q)) :=
        internalInnerMeasure_mono U hU hnewsub
      _ = μ T + internalInnerMeasure U hU (P + Q) := by
        rw [internalInnerMeasure_eq_add_sdiff U hU (T ∪ (P + Q)) T hTm subset_union_left,
          difference (P + Q) hPQsub]
  rw [hwhole] at hupper
  exact le_antisymm (internalInnerMeasure_mono U hU hPQsub)
    ((ENNReal.add_le_add_iff_left (measure_ne_top μ T)).mp hupper)

end Erdos335.Loeb

end
