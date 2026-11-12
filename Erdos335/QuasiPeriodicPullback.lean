import Erdos335.LoebCompactEqualityReduction
import Erdos335.QuasiPeriodicSets

/-!
# Pulling back quasi-periodic decompositions

A surjective measurable homomorphism preserves the exact coset data and
the almost-periodicity of the background. For pair data, the inner measure
of the active sum must also be preserved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {G K : Type*} [AddCommGroup G] [AddCommGroup K]
variable [MeasurableSpace G] [MeasurableSpace K]

theorem preimage_vadd_subgroup (φ : G →+ K) (H : AddSubgroup K) (a : G) :
    φ ⁻¹' (φ a +ᵥ (H : Set K)) = a +ᵥ (H.comap φ : Set G) := by
  ext x
  constructor
  · rintro ⟨k, hk, heq⟩
    refine ⟨x - a, ?_, ?_⟩
    · change φ (x - a) ∈ H
      have hdiff : φ (x - a) = k := by
        rw [map_sub, ← heq]
        change φ a + k - φ a = k
        abel
      rwa [hdiff]
    · change a + (x - a) = x
      abel
  · rintro ⟨h, hh, rfl⟩
    change φ (a + h) ∈ φ a +ᵥ (H : Set K)
    exact ⟨φ h, hh, by simp only [vadd_eq_add, map_add]⟩

def QuasiPeriodicDecomposition.comap
    {μ : Measure G} (φ : G →+ K) (hφ : Measurable φ)
    (hsurj : Function.Surjective φ) {H : AddSubgroup K} {A : Set K}
    (p : QuasiPeriodicDecomposition (Measure.map φ μ) H A)
    (a : G) (ha : φ a = p.anchor) :
    QuasiPeriodicDecomposition μ (H.comap φ) (φ ⁻¹' A) where
  active := φ ⁻¹' p.active
  background := φ ⁻¹' p.background
  anchor := a
  active_measurable := p.active_measurable.preimage hφ
  background_measurable := p.background_measurable.preimage hφ
  active_nonempty := by
    obtain ⟨y, hy⟩ := p.active_nonempty
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, by change φ x ∈ p.active; rwa [hx]⟩
  partition := (congrArg (fun S : Set K => φ ⁻¹' S) p.partition).trans preimage_union
  active_subset_coset := by
    rw [← preimage_vadd_subgroup φ H a, ha]
    exact preimage_mono p.active_subset_coset
  separated := by
    apply Set.disjoint_left.mpr
    rintro x ⟨u, hu, k, hk, rfl⟩ hx
    exact Set.disjoint_left.mp p.separated
      ⟨φ u, hu, φ k, hk, (map_add φ u k).symm⟩ hx
  background_periodic := by
    have hsub : ((φ ⁻¹' p.background) + (H.comap φ : Set G)) \ (φ ⁻¹' p.background) ⊆
        φ ⁻¹' ((p.background + (H : Set K)) \ p.background) := by
      rintro x ⟨⟨u, hu, k, hk, rfl⟩, hx⟩
      exact ⟨⟨φ u, hu, φ k, hk, (map_add φ u k).symm⟩, hx⟩
    exact measure_mono_null hsub
      (Measure.preimage_null_of_map_null hφ.aemeasurable p.background_periodic)

theorem exists_quasiPeriodicPairData_comap
    {μ : Measure G} (φ : G →+ K) (hφ : Measurable φ)
    (hsurj : Function.Surjective φ) {A B : Set K}
    {innerK : Set K → ℝ≥0∞} (innerG : Set G → ℝ≥0∞)
    (p : QuasiPeriodicPairData (Measure.map φ μ) innerK A B)
    (hinner : innerG (φ ⁻¹' (p.left.active + p.right.active)) =
      innerK (p.left.active + p.right.active)) :
    ∃ r : QuasiPeriodicPairData μ innerG (φ ⁻¹' A) (φ ⁻¹' B),
      r.period = p.period.comap φ ∧
      r.left.active = φ ⁻¹' p.left.active ∧
      r.right.active = φ ⁻¹' p.right.active := by
  obtain ⟨a, ha⟩ := hsurj p.left.anchor
  obtain ⟨b, hb⟩ := hsurj p.right.anchor
  let left := p.left.comap φ hφ hsurj a ha
  let right := p.right.comap φ hφ hsurj b hb
  let r : QuasiPeriodicPairData μ innerG (φ ⁻¹' A) (φ ⁻¹' B) := {
    period := p.period.comap φ
    period_measurable := p.period_measurable.preimage hφ
    period_positive := by
      change 0 < μ (φ ⁻¹' (p.period : Set K))
      rw [← Measure.map_apply hφ p.period_measurable]
      exact p.period_positive
    left := left
    right := right
    nonempty_background := by
      rcases p.nonempty_background with ⟨y, hy⟩ | ⟨y, hy⟩
      · obtain ⟨x, hx⟩ := hsurj y
        exact Or.inl ⟨x, by change φ x ∈ p.left.background; rwa [hx]⟩
      · obtain ⟨x, hx⟩ := hsurj y
        exact Or.inr ⟨x, by change φ x ∈ p.right.background; rwa [hx]⟩
    unique_expression := by
      intro x hx y hy hxy
      change x + y ∈ (a + b) +ᵥ (p.period.comap φ : Set G) at hxy
      rw [← preimage_vadd_subgroup φ p.period (a + b)] at hxy
      change φ (x + y) ∈ φ (a + b) +ᵥ (p.period : Set K) at hxy
      rw [map_add, map_add, ha, hb] at hxy
      obtain ⟨hxcoset, hycoset⟩ := p.unique_expression (φ x) hx (φ y) hy hxy
      constructor
      · change x ∈ a +ᵥ (p.period.comap φ : Set G)
        rw [← preimage_vadd_subgroup φ p.period a, ha]
        exact hxcoset
      · change y ∈ b +ᵥ (p.period.comap φ : Set G)
        rw [← preimage_vadd_subgroup φ p.period b, hb]
        exact hycoset
    active_identity := by
      change innerG ((φ ⁻¹' p.left.active) + (φ ⁻¹' p.right.active)) =
        μ (φ ⁻¹' p.left.active) + μ (φ ⁻¹' p.right.active)
      rw [← preimage_add_of_surjective_addHom φ hsurj, hinner, p.active_identity,
        Measure.map_apply hφ p.left.active_measurable,
        Measure.map_apply hφ p.right.active_measurable]
  }
  exact ⟨r, rfl, rfl, rfl⟩

end Erdos335.Loeb

end
