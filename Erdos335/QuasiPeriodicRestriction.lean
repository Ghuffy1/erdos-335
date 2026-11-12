import Erdos335.QuasiPeriodicSets

/-!
# Restricting quasi-periodic data to full-measure subsets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
variable {μ : Measure G} {H : AddSubgroup G} {A B : Set G}

theorem QuasiPeriodicPairData.active_sum_eq_inter
    {inner : Set G → ℝ≥0∞} (p : QuasiPeriodicPairData μ inner A B) :
    p.left.active + p.right.active =
      (A + B) ∩ ((p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G)) := by
  apply subset_antisymm
  · rintro z ⟨a, ha, b, hb, rfl⟩
    refine ⟨add_mem_add ((subset_union_right.trans p.left.partition.ge) ha)
      ((subset_union_right.trans p.right.partition.ge) hb), ?_⟩
    obtain ⟨u, hu, hua⟩ := p.left.active_subset_coset ha
    obtain ⟨v, hv, hvb⟩ := p.right.active_subset_coset hb
    refine ⟨u + v, p.period.add_mem hu hv, ?_⟩
    change p.left.anchor + u = a at hua
    change p.right.anchor + v = b at hvb
    change (p.left.anchor + p.right.anchor) + (u + v) = a + b
    rw [← hua, ← hvb]
    abel
  · rintro z ⟨⟨a, ha, b, hb, rfl⟩, hz⟩
    obtain ⟨hacoset, hbcoset⟩ := p.unique_expression a ha b hb hz
    apply add_mem_add
    · rw [p.left.active_eq_inter_coset]
      exact ⟨ha, hacoset⟩
    · rw [p.right.active_eq_inter_coset]
      exact ⟨hb, hbcoset⟩

def QuasiPeriodicDecomposition.restrict
    (p : QuasiPeriodicDecomposition μ H A) (A₀ : Set G)
    (hA₀ : A₀ ⊆ A) (hA₀m : MeasurableSet A₀)
    (hnull : μ (A \ A₀) = 0) (hactive : (p.active ∩ A₀).Nonempty) :
    QuasiPeriodicDecomposition μ H A₀ where
  active := p.active ∩ A₀
  background := p.background ∩ A₀
  anchor := p.anchor
  active_measurable := p.active_measurable.inter hA₀m
  background_measurable := p.background_measurable.inter hA₀m
  active_nonempty := hactive
  partition := by
    ext x
    constructor
    · intro hx
      have hxA := hA₀ hx
      rw [p.partition] at hxA
      exact hxA.elim (fun hb => Or.inl ⟨hb, hx⟩) (fun ha => Or.inr ⟨ha, hx⟩)
    · exact fun hx => hx.elim (fun hb => hb.2) (fun ha => ha.2)
  active_subset_coset := inter_subset_left.trans p.active_subset_coset
  separated := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, k, hk, rfl⟩ hx
    exact Set.disjoint_left.mp p.separated (add_mem_add ha.1 hk) hx.1
  background_periodic := by
    have hsub : ((p.background ∩ A₀) + (H : Set G)) \ (p.background ∩ A₀) ⊆
        ((p.background + (H : Set G)) \ p.background) ∪ (A \ A₀) := by
      rintro x ⟨⟨b, hb, k, hk, rfl⟩, hx⟩
      by_cases hbg : b + k ∈ p.background
      · right
        refine ⟨(subset_union_left.trans p.partition.ge) hbg, ?_⟩
        exact fun h₀ => hx ⟨hbg, h₀⟩
      · exact Or.inl ⟨add_mem_add hb.1 hk, hbg⟩
    apply measure_mono_null hsub
    apply nonpos_iff_eq_zero.mp
    calc
      μ (((p.background + (H : Set G)) \ p.background) ∪ (A \ A₀)) ≤
          μ ((p.background + (H : Set G)) \ p.background) + μ (A \ A₀) := measure_union_le _ _
      _ = 0 := by rw [p.background_periodic, hnull, add_zero]

end Erdos335.Loeb

end
