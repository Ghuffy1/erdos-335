import Erdos335.LoebQuasiPeriodicOutputRecovery
import Erdos335.LoebQuasiPeriodicBackground

/-!
# Recovering a pair from a quasi-periodic pair with the same sumset
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicSumModelLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

def QuasiPeriodicPairData.loebSum
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))}
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hSm : MeasurableSet (A + B)) :
    QuasiPeriodicDecomposition (loebMeasure U hU) p.period (A + B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let T := (p.left.background + B) ∪ (A + p.right.background)
  let R := p.left.active + p.right.active
  have hTm := (loeb_quasiPeriodic_background U hU q A B (internalInnerMeasure U hU) p).1
  have hTp := (loeb_quasiPeriodic_background U hU q A B (internalInnerMeasure U hU) p).2
  have hsplit : A + B = T ∪ R := p.sum_partition
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
  have hRset : R = (A + B) \ T := by
    rw [hsplit]
    ext x
    constructor
    · intro hx
      exact ⟨Or.inr hx, fun ht => Set.disjoint_left.mp hTR ht hx⟩
    · rintro ⟨ht | hx, hn⟩
      · exact False.elim (hn ht)
      · exact hx
  have hRm : MeasurableSet R := hRset.symm ▸ hSm.diff hTm
  have hRsat : R + (p.period : Set G) ⊆
      (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) := by
    rintro z ⟨x, hx, k, hk, rfl⟩
    obtain ⟨l, hl, hlx⟩ := hRcoset hx
    refine ⟨l + k, p.period.add_mem hl hk, ?_⟩
    change (p.left.anchor + p.right.anchor) + l = x at hlx
    change (p.left.anchor + p.right.anchor) + (l + k) = x + k
    rw [← hlx]
    exact (add_assoc _ _ _).symm
  have hRne : R.Nonempty := by
    obtain ⟨x, hx⟩ := p.left.active_nonempty
    obtain ⟨y, hy⟩ := p.right.active_nonempty
    exact ⟨x + y, add_mem_add hx hy⟩
  exact {
    active := R
    background := T
    anchor := p.left.anchor + p.right.anchor
    active_measurable := hRm
    background_measurable := hTm
    active_nonempty := hRne
    partition := hsplit
    active_subset_coset := hRcoset
    separated := (p.background_disjoint_active_coset.mono_right hRsat).symm
    background_periodic := ae_le_set.mp hTp.le
  }

theorem loeb_quasiPeriodic_pair_of_equal_sum_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B P Q : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) P Q)
    (hPQm : MeasurableSet (P + Q))
    (hPQae : P + Q =ᵐ[loebMeasure U hU] A + B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hCpos : 0 < loebMeasure U hU (A + B)ᶜ)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let r := p.loebSum U hU q hPQm
  have hactive : 0 < μ r.active := (loeb_quasiPeriodic_active_mass_bounds U hU q
    (A + B) (P + Q) p.period r hPQae
    (hnoAE p.period p.period_measurable p.period_positive)).1
  have hbgne : r.background.Nonempty := by
    rcases p.nonempty_background with ⟨x, hx⟩ | ⟨y, hy⟩
    · obtain ⟨y, hy⟩ := p.right.active_nonempty
      exact ⟨x + y, Or.inl (add_mem_add hx ((subset_union_right.trans p.right.partition.ge) hy))⟩
    · obtain ⟨x, hx⟩ := p.left.active_nonempty
      exact ⟨x + y, Or.inr (add_mem_add ((subset_union_right.trans p.left.partition.ge) hx) hy)⟩
  obtain ⟨t, ht⟩ := hbgne
  have hHbound : μ (p.period : Set G) ≤ μ r.background := by
    rw [← loeb_measure_section_eq_of_essential_period U hU p.period r.background
      r.background_measurable r.background_periodic t ht]
    exact measure_mono inter_subset_left
  have hparts : Disjoint r.background r.active := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp r.separated ⟨x, hy, 0, p.period.zero_mem, add_zero x⟩ hx
  have hmass : μ (P + Q) = μ r.background + μ r.active :=
    (congrArg μ r.partition).trans (measure_union hparts r.active_measurable)
  have hlarge : μ (p.period : Set G) < μ (A + B) := by
    rw [← measure_congr hPQae, hmass]
    exact hHbound.trans_lt (ENNReal.lt_add_right (measure_ne_top μ _) hactive.ne')
  exact loeb_quasiPeriodic_pair_of_large_output_model U hU q A B (P + Q) p.period
    p.period_measurable p.period_positive r hPQae hAm hBm hSm hApos hBpos hCpos
    hlarge hfull hirr hne hnoAE

end Erdos335.Loeb

end
