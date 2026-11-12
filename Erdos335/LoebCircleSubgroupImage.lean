import Erdos335.LoebPositiveSubgroups
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Positive Loeb subgroups map onto a surjective circle factor
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory

noncomputable section

namespace Erdos335.Loeb

local instance circleSubgroupImageLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem surjective_circle_restriction_of_positive_loeb_subgroup
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hsurj : Function.Surjective φ)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    Function.Surjective (φ.comp H.subtype) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨h, p, _, hker, _⟩ :=
    positive_measurable_subgroup_is_natural_finite_kernel U hU q H hH hHpos
  intro z
  let w : AddCircle (1 : ℝ) := DivisibleBy.div z ((h : ℕ) : ℤ)
  have hnonzero : ((h : ℕ) : ℤ) ≠ 0 := by exact_mod_cast h.pos.ne'
  have hw : ((h : ℕ) : ℤ) • w = z := DivisibleBy.div_cancel z hnonzero
  obtain ⟨g, hg⟩ := hsurj w
  have hmem : ((h : ℕ) : ℤ) • g ∈ H := by
    rw [← hker]
    change (finiteQuotient U p) (((h : ℕ) : ℤ) • g) = 0
    rw [map_zsmul]
    simp [zsmul_eq_mul]
  refine ⟨⟨((h : ℕ) : ℤ) • g, hmem⟩, ?_⟩
  change φ (((h : ℕ) : ℤ) • g) = z
  rw [map_zsmul, hg]
  exact hw

end Erdos335.Loeb

end
