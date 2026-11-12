import Erdos335.LoebSparseCoset

/-!
# Finite representatives for occupied cosets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem exists_finite_coset_cover
    {G F : Type*} [AddCommGroup G] [AddCommGroup F] [Finite F]
    (φ : G →+ F) (A : Set G) :
    ∃ R : Finset G, (R : Set G) ⊆ A ∧
      A + (φ.ker : Set G) = (R : Set G) + (φ.ker : Set G) := by
  classical
  let I := φ '' A
  let rep : I → G := fun y => Classical.choose y.property
  have hrepA (y : I) : rep y ∈ A := (Classical.choose_spec y.property).1
  have hrepφ (y : I) : φ (rep y) = y := (Classical.choose_spec y.property).2
  let R := (Set.finite_range rep).toFinset
  have hR (x : G) : x ∈ R ↔ ∃ y : I, rep y = x := by simp [R]
  have hRA : (R : Set G) ⊆ A := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hR x).mp hx
    exact hrepA y
  refine ⟨R, hRA, subset_antisymm ?_ (add_subset_add hRA Subset.rfl)⟩
  rintro x ⟨a, ha, k, hk, rfl⟩
  let y : I := ⟨φ a, ⟨a, ha, rfl⟩⟩
  have hker : a - rep y ∈ φ.ker := by
    change φ (a - rep y) = 0
    rw [map_sub, hrepφ]
    exact sub_self (φ a)
  refine ⟨rep y, (hR _).mpr ⟨y, rfl⟩, (a - rep y) + k, φ.ker.add_mem hker hk, ?_⟩
  abel

local instance finiteCosetCoverLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_exists_finite_coset_cover
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) :
    ∃ R : Finset ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      (R : Set _) ⊆ A ∧ A + (H : Set _) = (R : Set _) + (H : Set _) := by
  obtain ⟨h, p, _, hker, _⟩ :=
    positive_measurable_subgroup_is_natural_finite_kernel U hU q H hHm hHpos
  simpa only [hker] using exists_finite_coset_cover (finiteQuotient U p) A

end Erdos335.Loeb

end
