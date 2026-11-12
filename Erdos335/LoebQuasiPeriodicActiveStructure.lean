import Erdos335.LoebQuasiPeriodicIrreducible
import Erdos335.LoebNonextendiblePeriods
import Erdos335.LoebFinitePeriodIntersection
import Erdos335.LoebEssentialStabilizer

/-!
# Structural hypotheses inherited by the active pair

A positive quasi-periodic active pair inherits irreducibility and the
absence of positive subgroups of translation periods. Its equality
identity then gives nonextendibility.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicActiveStructureLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_active_structure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU p.left.active) (hBpos : 0 < loebMeasure U hU p.right.active)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    MeasurableSet (p.left.active + p.right.active) ∧
    MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) p.left.active p.right.active ∧
    MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) p.left.active p.right.active ∧
    ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ (p.left.active + p.right.active) =ᵐ[loebMeasure U hU]
        p.left.active + p.right.active := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let T := (p.left.background + B) ∪ (A + p.right.background)
  let R := p.left.active + p.right.active
  obtain ⟨hTm, hTp⟩ := loeb_quasiPeriodic_background U hU q A B (internalInnerMeasure U hU) p
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
  have hRnoAE : ∀ H : AddSubgroup G, MeasurableSet (H : Set G) → 0 < μ (H : Set G) →
      ¬ ∀ t ∈ H, t +ᵥ R =ᵐ[μ] R := by
    intro H hHm hHpos hp
    obtain ⟨hJm, hJpos⟩ := loeb_positive_subgroup_intersection U hU q p.period H
      p.period_measurable hHm p.period_positive hHpos
    apply hnoAE (p.period ⊓ H) hJm hJpos
    intro t ht
    have hleft := loeb_translate_ae_of_essential_period U hU q T hTm p.period
      (ae_le_set.mp hTp.le) t ht.1
    have hright := hp t ht.2
    rw [hsplit, vadd_set_union]
    filter_upwards [hleft, hright] with x hx hy
    change (x ∈ t +ᵥ T ∨ x ∈ t +ᵥ R) = (x ∈ T ∨ x ∈ R)
    rw [hx, hy]
  have hRne : MeasureNonextendible μ (internalInnerMeasure U hU) p.left.active p.right.active := by
    apply loeb_nonextendible_of_no_essential_period U hU q p.left.active p.right.active
      p.left.active_measurable p.right.active_measurable hApos hBpos p.active_identity
    intro h hp
    apply hRnoAE (naturalCyclicKernel U q h) (measurable_naturalCyclicKernel U q h)
      (naturalCyclicKernel_measure_pos U hU q h)
    intro t ht
    exact loeb_translate_ae_of_essential_period U hU q R hRm (naturalCyclicKernel U q h)
      (ae_le_set.mp hp.le) t ht
  exact ⟨hRm, loeb_quasiPeriodic_active_irreducible U hU q A B p hirr, hRne, hRnoAE⟩

end Erdos335.Loeb

end
