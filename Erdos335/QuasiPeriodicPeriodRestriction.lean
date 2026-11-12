import Erdos335.LoebIntegerPrefixes

/-!
# Restricting the period when the active inputs occupy smaller cosets
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
variable {μ : Measure G} {H K : AddSubgroup G} {A B : Set G}

theorem QuasiPeriodicDecomposition.anchor_mem_of_smaller_coset
    (p : QuasiPeriodicDecomposition μ H A) (hKH : K ≤ H) (a : G)
    (hactive : p.active ⊆ a +ᵥ (K : Set G)) : a ∈ p.anchor +ᵥ (H : Set G) := by
  obtain ⟨x, hx⟩ := p.active_nonempty
  obtain ⟨h, hh, hhx⟩ := p.active_subset_coset hx
  obtain ⟨k, hk, hkx⟩ := hactive hx
  refine ⟨h - k, H.sub_mem hh (hKH hk), ?_⟩
  change p.anchor + h = x at hhx
  change a + k = x at hkx
  change p.anchor + (h - k) = a
  calc
    p.anchor + (h - k) = (p.anchor + h) - k := by abel
    _ = x - k := by rw [hhx]
    _ = a := by rw [← hkx]; abel

def QuasiPeriodicDecomposition.restrictPeriod
    (p : QuasiPeriodicDecomposition μ H A) (hKH : K ≤ H) (a : G)
    (hactive : p.active ⊆ a +ᵥ (K : Set G)) : QuasiPeriodicDecomposition μ K A where
  active := p.active
  background := p.background
  anchor := a
  active_measurable := p.active_measurable
  background_measurable := p.background_measurable
  active_nonempty := p.active_nonempty
  partition := p.partition
  active_subset_coset := hactive
  separated := p.separated.mono_left (add_subset_add Subset.rfl hKH)
  background_periodic := measure_mono_null (sdiff_subset_sdiff_left (add_subset_add Subset.rfl hKH))
    p.background_periodic

def QuasiPeriodicPairData.restrictPeriod
    {inner : Set G → ℝ≥0∞} (p : QuasiPeriodicPairData μ inner A B)
    (K : AddSubgroup G) (hKm : MeasurableSet (K : Set G)) (hKpos : 0 < μ (K : Set G))
    (hKH : K ≤ p.period) (a b : G)
    (hleft : p.left.active ⊆ a +ᵥ (K : Set G))
    (hright : p.right.active ⊆ b +ᵥ (K : Set G)) : QuasiPeriodicPairData μ inner A B where
  period := K
  period_measurable := hKm
  period_positive := hKpos
  left := p.left.restrictPeriod hKH a hleft
  right := p.right.restrictPeriod hKH b hright
  nonempty_background := p.nonempty_background
  unique_expression := by
    intro x hx y hy hxy
    obtain ⟨h, hh, hha⟩ := p.left.anchor_mem_of_smaller_coset hKH a hleft
    obtain ⟨k, hk, hkb⟩ := p.right.anchor_mem_of_smaller_coset hKH b hright
    have houter : x + y ∈ (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) := by
      obtain ⟨l, hl, hlxy⟩ := hxy
      refine ⟨h + k + l, p.period.add_mem (p.period.add_mem hh hk) (hKH hl), ?_⟩
      change p.left.anchor + h = a at hha
      change p.right.anchor + k = b at hkb
      change (a + b) + l = x + y at hlxy
      change (p.left.anchor + p.right.anchor) + (h + k + l) = x + y
      calc
        (p.left.anchor + p.right.anchor) + (h + k + l) =
            ((p.left.anchor + h) + (p.right.anchor + k)) + l := by abel
        _ = x + y := by rw [hha, hkb, hlxy]
    obtain ⟨hxH, hyH⟩ := p.unique_expression x hx y hy houter
    have hxactive : x ∈ p.left.active := by rw [p.left.active_eq_inter_coset]; exact ⟨hx, hxH⟩
    have hyactive : y ∈ p.right.active := by rw [p.right.active_eq_inter_coset]; exact ⟨hy, hyH⟩
    exact ⟨hleft hxactive, hright hyactive⟩
  active_identity := p.active_identity

end Erdos335.Loeb

end
