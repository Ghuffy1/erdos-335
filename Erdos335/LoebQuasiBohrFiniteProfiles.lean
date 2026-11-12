import Erdos335.LoebQuasiBohrProfiles
import Erdos335.LoebBohrPairSwap

/-!
# Finite support and mass formulas for positive quasi-periodic terminals
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal BigOperators Classical

noncomputable section

namespace Erdos335.Loeb

local instance quasiBohrFiniteProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiBohr_left_residue_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (b : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U b.residue).ker)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (b.modulus : ℕ) ∣ (h : ℕ))
    (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h A r =
      if naturalCyclicProjection h b.modulus r = finiteQuotient U b.residue b.left_anchor
        then b.left_length
      else if naturalCyclicProjection h b.modulus r ∈ (finiteQuotient U b.residue) '' A
        then 1 else 0 := by
  exact loeb_quasiBohr_right_residue_profile U hU q B A p.swap b.swap hperiod h hd hmh r

theorem loeb_quasiBohr_right_mass
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (b : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U b.residue).ker)
    (hd : ∀ᶠ n in U, (b.modulus : ℕ) ∣ (q n : ℕ))
    (R : Finset (ZMod (b.modulus : ℕ)))
    (hR : (finiteQuotient U b.residue) '' B = (R : Set _)) :
    (loebMeasure U hU B).toReal = ((R.card : ℝ) - 1 + b.right_length) / (b.modulus : ℕ) := by
  let f := finiteQuotient U b.residue
  let c := f b.right_anchor
  have hc : c ∈ R := by
    obtain ⟨x, hx⟩ := p.right.active_nonempty
    have hxB : x ∈ B := (subset_union_right.trans p.right.partition.ge) hx
    have hfx : f x = c := by
      have hcos := (b.right_containment hx).1
      rwa [← addHom_fiber_eq_coset] at hcos
    change c ∈ (R : Set _)
    rw [← hR]
    exact ⟨x, hxB, hfx⟩
  have hid : naturalCyclicProjection b.modulus b.modulus = AddMonoidHom.id (ZMod (b.modulus : ℕ)) := by
    ext r
    rw [naturalCyclicProjection_val b.modulus b.modulus dvd_rfl, ZMod.natCast_zmod_val]
    rfl
  have hp (r : ZMod (b.modulus : ℕ)) : loebResidueProfile U hU q b.modulus B r =
      if r = c then b.right_length else if r ∈ R then 1 else 0 := by
    have hh := loeb_quasiBohr_right_residue_profile U hU q A B p b hperiod b.modulus hd dvd_rfl r
    simpa only [hid, AddMonoidHom.id_apply, hR, Finset.mem_coe] using hh
  have hpoint (r : ZMod (b.modulus : ℕ)) : loebResidueProfile U hU q b.modulus B r =
      (if r ∈ R then (1 : ℝ) else 0) + (if r = c then b.right_length - 1 else 0) := by
    rw [hp]
    by_cases hr : r = c
    · subst r
      simp only [ite_true, if_pos hc]
      ring
    · simp only [if_neg hr, add_zero]
  have hsum : (∑ r, loebResidueProfile U hU q b.modulus B r) = (R.card : ℝ) + (b.right_length - 1) := by
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp
  have hm := sum_loebResidueProfile U hU q b.modulus B
  rw [hsum] at hm
  apply (eq_div_iff (by exact_mod_cast b.modulus.ne_zero : ((b.modulus : ℕ) : ℝ) ≠ 0)).mpr
  nlinarith

end Erdos335.Loeb

end
