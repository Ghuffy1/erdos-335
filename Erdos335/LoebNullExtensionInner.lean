import Erdos335.LoebQuasiPeriodicAbsorption
import Erdos335.LoebInnerSplit

/-!
# The active inner-sum identity under an extension

The fixed measurable background is disjoint from the active output
coset. Its measure can be cancelled from the two equal total inner
measures, preserving the active sum's inner measure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance nullExtensionInnerLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_extension_active_inner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hfull : internalInnerMeasure U hU (A' + B') = internalInnerMeasure U hU (A + B)) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    internalInnerMeasure U hU ((A' ∩ (p.left.anchor +ᵥ (p.period : Set G))) +
      (B' ∩ (p.right.anchor +ᵥ (p.period : Set G)))) =
      internalInnerMeasure U hU (p.left.active + p.right.active) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let E := (p.left.background + B) ∪ (A + p.right.background)
  let oldActive := p.left.active + p.right.active
  let newLeft := A' ∩ (p.left.anchor +ᵥ (p.period : Set G))
  let newRight := B' ∩ (p.right.anchor +ᵥ (p.period : Set G))
  let newActive := newLeft + newRight
  have hEm : MeasurableSet E := (loeb_quasiPeriodic_background U hU q A B (internalInnerMeasure U hU) p).1
  have hES : E ⊆ A + B := subset_union_left.trans p.sum_partition.ge
  have hES' : E ⊆ A' + B' := hES.trans (add_subset_add hAA' hBB')
  have hNewSubCoset : newActive ⊆ (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) := by
    rintro x ⟨a, ⟨_, ⟨k, hk, hka⟩⟩, b, ⟨_, ⟨l, hl, hlb⟩⟩, rfl⟩
    refine ⟨k + l, p.period.add_mem hk hl, ?_⟩
    change p.left.anchor + k = a at hka
    change p.right.anchor + l = b at hlb
    change (p.left.anchor + p.right.anchor) + (k + l) = a + b
    rw [← hka, ← hlb]
    abel
  have hdisjoint : Disjoint E newActive := p.background_disjoint_active_coset.mono_right hNewSubCoset
  have hNewSub : newActive ⊆ (A' + B') \ E := by
    intro x hx
    refine ⟨add_subset_add inter_subset_left inter_subset_left hx, ?_⟩
    exact fun hxE => Set.disjoint_left.mp hdisjoint hxE hx
  have hOldDiff : (A + B) \ E = oldActive := by
    apply subset_antisymm
    · rintro x ⟨hx, hxout⟩
      exact (p.sum_partition ▸ hx).resolve_left hxout
    · intro x hx
      refine ⟨p.sum_partition.ge (Or.inr hx), ?_⟩
      intro hxE
      exact Set.disjoint_left.mp p.background_disjoint_active_coset hxE (p.active_sum_subset_coset hx)
  have hsplitOld := internalInnerMeasure_eq_add_sdiff U hU (A + B) E hEm hES
  rw [hOldDiff] at hsplitOld
  have hsplitNew := internalInnerMeasure_eq_add_sdiff U hU (A' + B') E hEm hES'
  have hupper : internalInnerMeasure U hU newActive ≤ internalInnerMeasure U hU oldActive := by
    apply (ENNReal.add_le_add_iff_left (measure_ne_top μ E)).mp
    calc
      μ E + internalInnerMeasure U hU newActive ≤ μ E + internalInnerMeasure U hU ((A' + B') \ E) :=
        add_le_add le_rfl (internalInnerMeasure_mono U hU hNewSub)
      _ = internalInnerMeasure U hU (A' + B') := hsplitNew.symm
      _ = internalInnerMeasure U hU (A + B) := hfull
      _ = μ E + internalInnerMeasure U hU oldActive := hsplitOld
  have hOldSub : oldActive ⊆ newActive := by
    apply add_subset_add
    · intro a ha
      exact ⟨hAA' ((subset_union_right.trans p.left.partition.ge) ha), p.left.active_subset_coset ha⟩
    · intro b hb
      exact ⟨hBB' ((subset_union_right.trans p.right.partition.ge) hb), p.right.active_subset_coset hb⟩
  exact le_antisymm hupper (internalInnerMeasure_mono U hU hOldSub)

end Erdos335.Loeb

end
