import Erdos335.LoebQuasiPeriodicData

/-!
# Set identities for quasi-periodic decompositions
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
variable {μ : Measure G} {H : AddSubgroup G} {A B : Set G}

theorem QuasiPeriodicDecomposition.active_add_period
    (p : QuasiPeriodicDecomposition μ H A) : p.active + (H : Set G) = p.anchor +ᵥ (H : Set G) := by
  apply subset_antisymm
  · rintro x ⟨a, ha, k, hk, rfl⟩
    obtain ⟨l, hl, hla⟩ := p.active_subset_coset ha
    refine ⟨l + k, H.add_mem hl hk, ?_⟩
    change p.anchor + l = a at hla
    rw [← hla]
    simp [vadd_eq_add, add_assoc]
  · obtain ⟨a, ha⟩ := p.active_nonempty
    obtain ⟨k, hk, hka⟩ := p.active_subset_coset ha
    rintro x ⟨l, hl, hlx⟩
    refine ⟨a, ha, l - k, H.sub_mem hl hk, ?_⟩
    change p.anchor + k = a at hka
    change p.anchor + l = x at hlx
    rw [← hka, ← hlx]
    simp only [vadd_eq_add]
    abel

theorem QuasiPeriodicDecomposition.active_eq_inter_coset
    (p : QuasiPeriodicDecomposition μ H A) : p.active = A ∩ (p.anchor +ᵥ (H : Set G)) := by
  apply subset_antisymm
  · intro x hx
    refine ⟨?_, p.active_subset_coset hx⟩
    rw [p.partition]
    exact Or.inr hx
  · rintro x ⟨hx, hxcoset⟩
    rw [p.partition] at hx
    rcases hx with hxbackground | hxactive
    · have hs : x ∈ p.active + (H : Set G) := by rwa [p.active_add_period]
      exact False.elim (Set.disjoint_left.mp p.separated hs hxbackground)
    · exact hxactive

theorem QuasiPeriodicDecomposition.background_eq_sdiff_coset
    (p : QuasiPeriodicDecomposition μ H A) : p.background = A \ (p.anchor +ᵥ (H : Set G)) := by
  apply subset_antisymm
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [p.partition]
      exact Or.inl hx
    · intro hxcoset
      have hs : x ∈ p.active + (H : Set G) := by rwa [p.active_add_period]
      exact Set.disjoint_left.mp p.separated hs hx
  · rintro x ⟨hx, hxout⟩
    rw [p.partition] at hx
    rcases hx with hxbackground | hxactive
    · exact hxbackground
    · exact False.elim (hxout (p.active_subset_coset hxactive))

theorem QuasiPeriodicPairData.sum_partition
    {inner : Set G → ℝ≥0∞} (p : QuasiPeriodicPairData μ inner A B) :
    A + B = ((p.left.background + B) ∪ (A + p.right.background)) ∪
      (p.left.active + p.right.active) := by
  apply subset_antisymm
  · rintro z ⟨x, hx, y, hy, rfl⟩
    have hx' := hx
    have hy' := hy
    rw [p.left.partition] at hx'
    rw [p.right.partition] at hy'
    rcases hx' with hxbackground | hxactive
    · exact Or.inl (Or.inl (add_mem_add hxbackground hy))
    rcases hy' with hybackground | hyactive
    · exact Or.inl (Or.inr (add_mem_add hx hybackground))
    · exact Or.inr (add_mem_add hxactive hyactive)
  · rintro z ((hz | hz) | hz)
    · exact add_subset_add (subset_union_left.trans p.left.partition.ge) Subset.rfl hz
    · exact add_subset_add Subset.rfl (subset_union_left.trans p.right.partition.ge) hz
    · exact add_subset_add (subset_union_right.trans p.left.partition.ge)
        (subset_union_right.trans p.right.partition.ge) hz

theorem QuasiPeriodicPairData.background_disjoint_active_coset
    {inner : Set G → ℝ≥0∞} (p : QuasiPeriodicPairData μ inner A B) :
    Disjoint ((p.left.background + B) ∪ (A + p.right.background))
      ((p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G)) := by
  apply Set.disjoint_left.mpr
  rintro z (hz | hz) hzcoset
  · obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hxA : x ∈ A := by rw [p.left.partition]; exact Or.inl hx
    have hxcoset := (p.unique_expression x hxA y hy hzcoset).1
    have hxsat : x ∈ p.left.active + (p.period : Set G) := by rwa [p.left.active_add_period]
    exact Set.disjoint_left.mp p.left.separated hxsat hx
  · obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hyB : y ∈ B := by rw [p.right.partition]; exact Or.inl hy
    have hycoset := (p.unique_expression x hx y hyB hzcoset).2
    have hysat : y ∈ p.right.active + (p.period : Set G) := by rwa [p.right.active_add_period]
    exact Set.disjoint_left.mp p.right.separated hysat hy

end Erdos335.Loeb

end
