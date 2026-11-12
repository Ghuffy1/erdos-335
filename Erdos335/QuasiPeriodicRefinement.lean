import Erdos335.QuasiPeriodicRestriction

/-!
# Refining the active pair of a quasi-periodic decomposition

This is the exact set-theoretic composition used in Griesmer's Lemma 10.14.
The smaller period is required to lie in the original period.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
variable {μ : Measure G} {H K : AddSubgroup G} {A B : Set G}

theorem QuasiPeriodicDecomposition.refinement_anchor_mem
    (p : QuasiPeriodicDecomposition μ H A)
    (r : QuasiPeriodicDecomposition μ K p.active) (hKH : K ≤ H) :
    r.anchor ∈ p.anchor +ᵥ (H : Set G) := by
  obtain ⟨x, hx⟩ := r.active_nonempty
  obtain ⟨k, hk, hkx⟩ := r.active_subset_coset hx
  obtain ⟨h, hh, hhx⟩ := p.active_subset_coset ((subset_union_right.trans r.partition.ge) hx)
  refine ⟨h - k, H.sub_mem hh (hKH hk), ?_⟩
  change r.anchor + k = x at hkx
  change p.anchor + h = x at hhx
  change p.anchor + (h - k) = r.anchor
  calc
    p.anchor + (h - k) = (p.anchor + h) - k := by abel
    _ = x - k := by rw [hhx]
    _ = r.anchor := by rw [← hkx]; abel

def QuasiPeriodicDecomposition.refine
    (p : QuasiPeriodicDecomposition μ H A)
    (r : QuasiPeriodicDecomposition μ K p.active) (hKH : K ≤ H) :
    QuasiPeriodicDecomposition μ K A where
  active := r.active
  background := p.background ∪ r.background
  anchor := r.anchor
  active_measurable := r.active_measurable
  background_measurable := p.background_measurable.union r.background_measurable
  active_nonempty := r.active_nonempty
  partition := p.partition.trans ((congrArg (fun S : Set G => p.background ∪ S) r.partition).trans
    (union_assoc p.background r.background r.active).symm)
  active_subset_coset := r.active_subset_coset
  separated := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, k, hk, rfl⟩ (hp | hr)
    · have hap : a ∈ p.active := (subset_union_right.trans r.partition.ge) ha
      exact Set.disjoint_left.mp p.separated (add_mem_add hap (hKH hk)) hp
    · exact Set.disjoint_left.mp r.separated (add_mem_add ha hk) hr
  background_periodic := by
    have hsub : (((p.background ∪ r.background) + (K : Set G)) \ (p.background ∪ r.background)) ⊆
        ((p.background + (H : Set G)) \ p.background) ∪ ((r.background + (K : Set G)) \ r.background) := by
      rintro x ⟨⟨a, (ha | ha), k, hk, rfl⟩, hout⟩
      · exact Or.inl ⟨add_mem_add ha (hKH hk), fun h => hout (Or.inl h)⟩
      · exact Or.inr ⟨add_mem_add ha hk, fun h => hout (Or.inr h)⟩
    apply measure_mono_null hsub
    apply nonpos_iff_eq_zero.mp
    calc
      μ (((p.background + (H : Set G)) \ p.background) ∪
          ((r.background + (K : Set G)) \ r.background)) ≤
        μ ((p.background + (H : Set G)) \ p.background) +
          μ ((r.background + (K : Set G)) \ r.background) := measure_union_le _ _
      _ = 0 := by rw [p.background_periodic, r.background_periodic, add_zero]

def QuasiPeriodicPairData.refine
    {inner : Set G → ℝ≥0∞} (p : QuasiPeriodicPairData μ inner A B)
    (r : QuasiPeriodicPairData μ inner p.left.active p.right.active)
    (hsub : r.period ≤ p.period) : QuasiPeriodicPairData μ inner A B where
  period := r.period
  period_measurable := r.period_measurable
  period_positive := r.period_positive
  left := p.left.refine r.left hsub
  right := p.right.refine r.right hsub
  nonempty_background := p.nonempty_background.elim
    (fun h => Or.inl (h.mono subset_union_left))
    (fun h => Or.inr (h.mono subset_union_left))
  unique_expression := by
    intro x hx y hy hxy
    obtain ⟨a, ha, hea⟩ := p.left.refinement_anchor_mem r.left hsub
    obtain ⟨b, hb, heb⟩ := p.right.refinement_anchor_mem r.right hsub
    have houter : x + y ∈ (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) := by
      obtain ⟨k, hk, heq⟩ := hxy
      refine ⟨a + b + k, p.period.add_mem (p.period.add_mem ha hb) (hsub hk), ?_⟩
      change p.left.anchor + a = r.left.anchor at hea
      change p.right.anchor + b = r.right.anchor at heb
      change (r.left.anchor + r.right.anchor) + k = x + y at heq
      change (p.left.anchor + p.right.anchor) + (a + b + k) = x + y
      calc
        (p.left.anchor + p.right.anchor) + (a + b + k) =
            ((p.left.anchor + a) + (p.right.anchor + b)) + k := by abel
        _ = x + y := by rw [hea, heb, heq]
    obtain ⟨hxcoset, hycoset⟩ := p.unique_expression x hx y hy houter
    have hxactive : x ∈ p.left.active := by rw [p.left.active_eq_inter_coset]; exact ⟨hx, hxcoset⟩
    have hyactive : y ∈ p.right.active := by rw [p.right.active_eq_inter_coset]; exact ⟨hy, hycoset⟩
    exact r.unique_expression x hxactive y hyactive hxy
  active_identity := r.active_identity

end Erdos335.Loeb

end
