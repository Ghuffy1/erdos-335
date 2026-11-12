import Erdos335.NaturalQuotientRefinement
import Erdos335.CyclicQuotients

/-!
# The aperiodic natural quotient of a subcritical finite sum
-/

set_option autoImplicit false

open Set
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem exists_finite_natural_critical_core (q : ℕ+)
    (S T : Finset (ZMod (q : ℕ))) (hS : S.Nonempty) (hT : T.Nonempty)
    (hsmall : (S + T).card < S.card + T.card) :
    ∃ h : ℕ+, (h : ℕ) ∣ (q : ℕ) ∧
      let π := naturalCyclicProjection q h
      ((S + T).image π).card + 1 = (S.image π).card + (T.image π).card ∧
      π ⁻¹' (((S + T).image π : Finset (ZMod (h : ℕ))) : Set (ZMod (h : ℕ))) =
        (S + T : Finset (ZMod (q : ℕ))) ∧
      (((S + T).image π).card : ℝ) / (h : ℕ) = ((S + T).card : ℝ) / (q : ℕ) := by
  classical
  let C := S + T
  let K := AddAction.stabilizer (ZMod (q : ℕ)) (C : Set (ZMod (q : ℕ)))
  have hC : C.Nonempty := hS.add hT
  obtain ⟨h, π, hindex, hdiv, hπ, hker, hnat⟩ := exists_natural_cyclic_quotient q K
  have hπeq : π = naturalCyclicProjection q h := by
    ext x
    rw [← ZMod.natCast_zmod_val x, hnat, naturalCyclicProjection_natCast q h hdiv]
  subst π
  have hcritical := critical_quotient_card_identity S T hS hT hsmall
    (naturalCyclicProjection q h) hπ hker
  have hKcoe : (K : Set (ZMod (q : ℕ))) = (C.addStab : Set (ZMod (q : ℕ))) :=
    (Finset.coe_addStab hC).symm
  have hsat : (C : Set (ZMod (q : ℕ))) + (K : Set (ZMod (q : ℕ))) = C := by
    rw [hKcoe, ← Finset.coe_add, Finset.add_addStab]
  have hpre : (naturalCyclicProjection q h) ⁻¹'
      ((C.image (naturalCyclicProjection q h) : Finset (ZMod (h : ℕ))) : Set (ZMod (h : ℕ))) = C := by
    rw [Finset.coe_image]
    rw [← addHom_saturation_eq_preimage_image, hker]
    exact hsat
  have hcount := card_stabilizer_quotient C C (naturalCyclicProjection q h) hπ hker
  rw [Finset.add_addStab] at hcount
  have hprod : C.addStab.card * (h : ℕ) = (q : ℕ) := by
    rw [hindex, ← natCard_stabilizer_eq_card C hC]
    simpa only [Nat.card_zmod] using K.card_mul_index
  have hcountR : (C.addStab.card : ℝ) * (C.image (naturalCyclicProjection q h)).card = C.card := by
    exact_mod_cast hcount
  have hprodR : (C.addStab.card : ℝ) * (h : ℕ) = (q : ℕ) := by exact_mod_cast hprod
  have hratio : ((C.image (naturalCyclicProjection q h)).card : ℝ) / (h : ℕ) =
      (C.card : ℝ) / (q : ℕ) := by
    have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
    have hq : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
    apply (div_eq_div_iff hh hq).mpr
    calc
      ((C.image (naturalCyclicProjection q h)).card : ℝ) * (q : ℕ) =
          (C.image (naturalCyclicProjection q h)).card * ((C.addStab.card : ℝ) * (h : ℕ)) := by rw [hprodR]
      _ = ((C.addStab.card : ℝ) * (C.image (naturalCyclicProjection q h)).card) * (h : ℕ) := by ring
      _ = (C.card : ℝ) * (h : ℕ) := by rw [hcountR]
  exact ⟨h, hdiv, hcritical.symm, hpre, hratio⟩

end Erdos335.Loeb

end
