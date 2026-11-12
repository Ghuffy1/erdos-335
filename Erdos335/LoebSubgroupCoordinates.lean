import Erdos335.LoebInternalEmbedding
import Erdos335.LoebPositiveSubgroups

/-!
# Cyclic coordinates on internal subgroups
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory

noncomputable section

namespace Erdos335.Loeb

def cyclicSubgroupOrders (q : ℕ → ℕ+) (K : ∀ n, AddSubgroup (ZMod (q n : ℕ))) : ℕ → ℕ+ :=
  fun n => ⟨Nat.card (K n), Nat.card_pos⟩

def cyclicSubgroupCoordinate (q : ℕ → ℕ+) (K : ∀ n, AddSubgroup (ZMod (q n : ℕ))) (n : ℕ) :
    ZMod (cyclicSubgroupOrders q K n : ℕ) →+ ZMod (q n : ℕ) :=
  (K n).subtype.comp (zmodAddCyclicAddEquiv (G := K n) inferInstance).toAddMonoidHom

theorem cyclicSubgroupCoordinate_injective
    (q : ℕ → ℕ+) (K : ∀ n, AddSubgroup (ZMod (q n : ℕ))) (n : ℕ) :
    Function.Injective (cyclicSubgroupCoordinate q K n) :=
  Subtype.coe_injective.comp (zmodAddCyclicAddEquiv (G := K n) inferInstance).injective

theorem cyclicSubgroupCoordinate_range
    (q : ℕ → ℕ+) (K : ∀ n, AddSubgroup (ZMod (q n : ℕ))) (n : ℕ) :
    Set.range (cyclicSubgroupCoordinate q K n) = (K n : Set (ZMod (q n : ℕ))) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (zmodAddCyclicAddEquiv (G := K n) inferInstance y).property
  · intro hx
    obtain ⟨y, hy⟩ := (zmodAddCyclicAddEquiv (G := K n) inferInstance).surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

theorem cyclicSubgroupCoordinates_range
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (K : ∀ n, AddSubgroup (ZMod (q n : ℕ))) :
    Set.range (productMapHom (U : Filter ℕ) (cyclicSubgroupCoordinate q K)) =
      (internalAddSubgroup U K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
  change Set.range (productMap (U : Filter ℕ) (fun n => cyclicSubgroupCoordinate q K n)) = _
  rw [range_productMap]
  change internalSet U (fun n => Set.range (cyclicSubgroupCoordinate q K n)) =
    internalSet U (fun n => (K n : Set (ZMod (q n : ℕ))))
  simp only [cyclicSubgroupCoordinate_range]

theorem positive_measurable_subgroup_has_cyclic_coordinates
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet[loebMeasurableSpace U]
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hpos : 0 < loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    ∃ r : ℕ → ℕ+, ∃ f : ∀ n, ZMod (r n : ℕ) →+ ZMod (q n : ℕ),
      (∀ n, Function.Injective (f n)) ∧
      Set.range (productMapHom (U : Filter ℕ) f) =
        (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
  obtain ⟨h, p, _, hker, _⟩ :=
    positive_measurable_subgroup_is_natural_finite_kernel U hU q H hH hpos
  let K := fun n => (p n).ker
  refine ⟨cyclicSubgroupOrders q K, cyclicSubgroupCoordinate q K,
    cyclicSubgroupCoordinate_injective q K, ?_⟩
  rw [cyclicSubgroupCoordinates_range, ← finiteQuotient_ker U p, hker]

end Erdos335.Loeb

end
