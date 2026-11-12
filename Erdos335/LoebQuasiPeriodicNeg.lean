import Erdos335.LoebAEPeriodOperations
import Erdos335.LoebQuasiPeriodicData

/-!
# Negation of quasi-periodic decompositions
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance quasiPeriodicNegLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

def QuasiPeriodicDecomposition.loebNeg
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    {A : Set ((U : Filter ℕ).Product X)} {H : AddSubgroup ((U : Filter ℕ).Product X)}
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A) :
    QuasiPeriodicDecomposition (loebMeasure U hU) H (-A) where
  active := -p.active
  background := -p.background
  anchor := -p.anchor
  active_measurable := p.active_measurable.preimage (measurable_loeb_neg U hU)
  background_measurable := p.background_measurable.preimage (measurable_loeb_neg U hU)
  active_nonempty := by
    obtain ⟨a, ha⟩ := p.active_nonempty
    exact ⟨-a, by simpa only [Set.mem_neg, neg_neg] using ha⟩
  partition := by
    have h := congrArg (fun S : Set ((U : Filter ℕ).Product X) => -S) p.partition
    have hUnion : -(p.background ∪ p.active) = (-p.background) ∪ (-p.active) := by
      ext x
      simp only [Set.mem_neg, mem_union]
    exact h.trans hUnion
  active_subset_coset := by
    intro x hx
    have hnegx : -x ∈ p.active := hx
    obtain ⟨k, hk, hkx⟩ := p.active_subset_coset hnegx
    refine ⟨-k, H.neg_mem hk, ?_⟩
    change p.anchor + k = -x at hkx
    change -p.anchor + -k = x
    calc
      -p.anchor + -k = -(p.anchor + k) := by abel
      _ = x := by rw [hkx, neg_neg]
  separated := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, h, hh, rfl⟩ hx
    have ha' : -a ∈ p.active := ha
    have hx' : -(a + h) ∈ p.background := hx
    apply Set.disjoint_left.mp p.separated _ hx'
    exact ⟨-a, ha', -h, H.neg_mem hh, by abel⟩
  background_periodic := by
    have hset : ((-p.background + (H : Set _)) \ (-p.background)) =
        -((p.background + (H : Set _)) \ p.background) := by
      rw [← neg_add_subgroup]
      ext x
      simp only [Set.mem_sdiff, Set.mem_neg]
    rw [hset, loebMeasure_neg U hU _ (measurable_of_loebMeasure_zero U hU _ p.background_periodic)]
    exact p.background_periodic

end Erdos335.Loeb

end
