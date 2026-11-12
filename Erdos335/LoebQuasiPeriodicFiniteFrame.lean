import Erdos335.LoebQuasiPeriodicSaturation

/-!
# The finite quotient frame of a quasi-periodic equality pair
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicFiniteFrameLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_finite_quotient_cardinality
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hSm : MeasurableSet (A + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (h : ℕ+) (ρ : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ))
    (hρ : ∀ᶠ n in U, Function.Surjective (ρ n))
    (hker : (finiteQuotient U ρ).ker = p.period)
    (S T : Finset (ZMod (h : ℕ)))
    (hS : (finiteQuotient U ρ) '' A = (S : Set (ZMod (h : ℕ))))
    (hT : (finiteQuotient U ρ) '' B = (T : Set (ZMod (h : ℕ)))) :
    (S + T).card + 1 = S.card + T.card := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let φ := finiteQuotient U ρ
  have mass (C : Set G) (R : Finset (ZMod (h : ℕ))) (hR : φ '' C = (R : Set (ZMod (h : ℕ)))) :
      (μ (C + (p.period : Set G))).toReal = (R.card : ℝ) / (h : ℕ) := by
    rw [← hker, addHom_saturation_eq_preimage_image, hR,
      loebMeasure_finiteQuotient_preimage U hU q ρ hρ,
      ENNReal.toReal_div, ENNReal.toReal_natCast]
    simp
  have hC : φ '' (A + B) = (↑(S + T) : Set (ZMod (h : ℕ))) := by
    rw [Set.image_add, hS, hT, Finset.coe_add]
  have hH : (μ (p.period : Set G)).toReal = 1 / (h : ℕ) := by
    rw [← hker, finiteQuotient_ker,
      loebMeasure_internalSubgroup_of_eventually_quotients U hU ρ hρ,
      ENNReal.toReal_div]
    simp
  have hreal := loeb_quasiPeriodic_saturated_equality U hU q A B p hSm hfull
  rw [mass A S hS, mass B T hT, mass (A + B) (S + T) hC, hH] at hreal
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  field_simp [hh] at hreal
  exact_mod_cast hreal.symm

theorem loeb_quasiPeriodic_finite_quotient_expression
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    {F : Type*} [AddCommGroup F] [Finite F]
    (φ : ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) →+ F)
    (hker : φ.ker = p.period) (S T : Finset F)
    (hS : φ '' A = (S : Set F)) (hT : φ '' B = (T : Set F)) :
    φ p.left.anchor ∈ S ∧ φ p.right.anchor ∈ T ∧
      ∀ r ∈ S, ∀ s ∈ T, r + s = φ p.left.anchor + φ p.right.anchor →
        r = φ p.left.anchor ∧ s = φ p.right.anchor := by
  have coset (x a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
      x ∈ a +ᵥ (p.period : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ↔ φ x = φ a := by
    rw [← hker, ← addHom_fiber_eq_coset]
    rfl
  have leftAnchor : φ p.left.anchor ∈ S := by
    obtain ⟨x, hx⟩ := p.left.active_nonempty
    have hxA : x ∈ A := (subset_union_right.trans p.left.partition.ge) hx
    have hφx := (coset x p.left.anchor).mp (p.left.active_subset_coset hx)
    change φ p.left.anchor ∈ (S : Set F)
    rw [← hS]
    exact ⟨x, hxA, hφx⟩
  have rightAnchor : φ p.right.anchor ∈ T := by
    obtain ⟨y, hy⟩ := p.right.active_nonempty
    have hyB : y ∈ B := (subset_union_right.trans p.right.partition.ge) hy
    have hφy := (coset y p.right.anchor).mp (p.right.active_subset_coset hy)
    change φ p.right.anchor ∈ (T : Set F)
    rw [← hT]
    exact ⟨y, hyB, hφy⟩
  refine ⟨leftAnchor, rightAnchor, ?_⟩
  intro r hr s hs hrs
  have hrA : r ∈ φ '' A := hS.symm ▸ hr
  have hsB : s ∈ φ '' B := hT.symm ▸ hs
  obtain ⟨x, hx, hxr⟩ := hrA
  obtain ⟨y, hy, hys⟩ := hsB
  have hsum : x + y ∈ (p.left.anchor + p.right.anchor) +ᵥ
      (p.period : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
    apply (coset (x + y) (p.left.anchor + p.right.anchor)).mpr
    rw [map_add, map_add, hxr, hys]
    exact hrs
  obtain ⟨hleft, hright⟩ := p.unique_expression x hx y hy hsum
  exact ⟨hxr.symm.trans ((coset x p.left.anchor).mp hleft),
    hys.symm.trans ((coset y p.right.anchor).mp hright)⟩

end Erdos335.Loeb

end
