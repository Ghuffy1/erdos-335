import Erdos335.LoebGeneralInverseIteration
import Erdos335.LoebFiniteFunctions

/-!
# Exact measure of finite quotient pullbacks
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise BigOperators

noncomputable section

namespace Erdos335.Loeb

local instance finiteQuotientMeasureLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem addHom_fiber_eq_coset {G F : Type*} [AddCommGroup G] [AddCommGroup F]
    (φ : G →+ F) (a : G) : φ ⁻¹' {φ a} = a +ᵥ (φ.ker : Set G) := by
  ext x
  constructor
  · intro hx
    have heq : φ x = φ a := hx
    refine ⟨x - a, ?_, by simp only [vadd_eq_add]; abel⟩
    change φ (x - a) = 0
    rw [map_sub, heq, sub_self]
  · rintro ⟨k, hk, rfl⟩
    change φ (a + k) = φ a
    rw [map_add, show φ k = 0 from hk, add_zero]

theorem loebMeasure_finiteQuotient_preimage
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {F : Type*} [AddCommGroup F] [Finite F]
    (p : ∀ n, ZMod (q n : ℕ) →+ F) (hp : ∀ᶠ n in U, Function.Surjective (p n))
    (S : Finset F) :
    loebMeasure U hU ((finiteQuotient U p) ⁻¹' (S : Set F)) =
      (S.card : ℝ≥0∞) / (Nat.card F : ℝ≥0∞) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let φ := finiteQuotient U p
  have hfun : finiteFunction U (fun n => p n) = (φ : G → F) := by
    funext x
    induction x using Quotient.inductionOn with
    | h a => rfl
  have hmeas (y : F) : MeasurableSet (φ ⁻¹' {y}) := by
    rw [← hfun, finiteFunction_preimage]
    exact measurable_internalSet U _
  have hker : μ (φ.ker : Set G) = 1 / (Nat.card F : ℝ≥0∞) := by
    rw [show φ.ker = internalAddSubgroup U (fun n => (p n).ker) from finiteQuotient_ker U p]
    exact loebMeasure_internalSubgroup_of_eventually_quotients U hU p hp
  have hfiber (y : F) : μ (φ ⁻¹' {y}) = 1 / (Nat.card F : ℝ≥0∞) := by
    obtain ⟨a, rfl⟩ := finiteQuotient_surjective_of_eventually U p hp y
    rw [addHom_fiber_eq_coset, loebMeasure_coset U hU φ.ker a]
    exact hker
  calc
    μ (φ ⁻¹' (S : Set F)) = ∑ y ∈ S, μ (φ ⁻¹' {y}) :=
      (sum_measure_preimage_singleton S (fun y _ => hmeas y)).symm
    _ = ∑ _y ∈ S, 1 / (Nat.card F : ℝ≥0∞) := Finset.sum_congr rfl (fun y _ => hfiber y)
    _ = _ := by simp [div_eq_mul_inv]

end Erdos335.Loeb

end
