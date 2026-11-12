import Erdos335.LoebIrreduciblePeriods
import Erdos335.LoebPeriodic

/-!
# Nontrivial active mass in an aperiodic quasi-periodic model
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicActiveBoundsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_active_mass_bounds
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H D)
    (hDS : D =ᵐ[loebMeasure U hU] S)
    (hnot : ¬ ∀ t ∈ H, t +ᵥ S =ᵐ[loebMeasure U hU] S) :
    0 < loebMeasure U hU p.active ∧
      loebMeasure U hU p.active < loebMeasure U hU
        (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hDm : MeasurableSet D := p.partition.symm ▸ (p.background_measurable.union p.active_measurable)
  have transfer (hp : ∀ t ∈ H, t +ᵥ D =ᵐ[μ] D) : False := by
    apply hnot
    intro t ht
    exact (loeb_vadd_congr_ae U hU S D t hDS.symm).trans ((hp t ht).trans hDS)
  have hpos : 0 < μ p.active := by
    by_contra hn
    exact transfer (loeb_quasiPeriodic_null_active_ae_periods U hU q D H p
      (le_antisymm (not_lt.mp hn) bot_le))
  refine ⟨hpos, ?_⟩
  have hle : μ p.active ≤ μ (H : Set G) :=
    (measure_mono p.active_subset_coset).trans_eq (loebMeasure_coset U hU H p.anchor)
  by_contra hn
  have heq : μ p.active = μ (H : Set G) := le_antisymm hle (not_lt.mp hn)
  let K := p.anchor +ᵥ (H : Set G)
  have hKH : K + (H : Set G) = K := by
    dsimp only [K]
    rw [vadd_set_add_eq, coe_add_coe]
  have hsub : p.active + (H : Set G) ⊆ K := by
    intro x hx
    have hm := add_subset_add p.active_subset_coset (show (H : Set G) ⊆ H from Subset.rfl) hx
    rwa [hKH] at hm
  have hKnull : μ (K \ p.active) = 0 := by
    rw [measure_sdiff p.active_subset_coset p.active_measurable.nullMeasurableSet (measure_ne_top μ _),
      show μ K = μ (H : Set G) from loebMeasure_coset U hU H p.anchor, heq, tsub_self]
  have hActperiod : μ ((p.active + (H : Set G)) \ p.active) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left hsub) hKnull
  have hDperiod : μ ((D + (H : Set G)) \ D) = 0 :=
    (congrArg (fun T => μ ((T + (H : Set G)) \ T)) p.partition).trans
      (almost_periodic_union U hU p.background p.active H p.background_periodic hActperiod)
  exact transfer (fun t ht => loeb_translate_ae_of_essential_period U hU q D hDm H hDperiod t ht)

end Erdos335.Loeb

end
