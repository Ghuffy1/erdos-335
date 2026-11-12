import Erdos335.LoebBohrSumModel
import Erdos335.LoebQuasiRefinedProfiles
import Erdos335.LoebQuasiPeriodicSaturation

/-!
# Refined output profiles of a positive quasi-periodic Bohr terminal
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal Classical

noncomputable section

namespace Erdos335.Loeb

local instance quasiBohrOutputProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiBohr_output_residue_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hSm : MeasurableSet (A + B))
    (b : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U b.residue).ker)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (b.modulus : ℕ) ∣ (h : ℕ))
    (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h (A + B) r =
      if naturalCyclicProjection h b.modulus r =
          finiteQuotient U b.residue (b.left_anchor + b.right_anchor)
        then b.left_length + b.right_length
      else if naturalCyclicProjection h b.modulus r ∈ (finiteQuotient U b.residue) '' (A + B)
        then 1 else 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let f := finiteQuotient U b.residue
  let d := loeb_quasiPeriodic_sum_decomposition U hU q A B p hSm
  have hActm : MeasurableSet (p.left.active + p.right.active) := d.active_measurable
  have hactiveFull : loebMeasure U hU (p.left.active + p.right.active) =
      loebMeasure U hU p.left.active + loebMeasure U hU p.right.active := by
    rw [← internalInnerMeasure_eq U hU _ hActm]
    exact p.active_identity
  have hsumModel := b.sum_model d.active_measurable hactiveFull
  have hquotient : f = finiteQuotient U (fun n => naturalCyclicProjection (q n) b.modulus) := by
    apply finiteQuotient_eq_of_eventually_natural
    · exact b.natural_residue.mono fun n hn => hn.2
    · exact hd.mono fun n hn k => naturalCyclicProjection_natCast (q n) b.modulus (dvd_trans hmh hn) k
  have anchor_eq (V : Set G) (z : QuasiPeriodicDecomposition (loebMeasure U hU) p.period V)
      (a : G) (hcontained : z.active ⊆ a +ᵥ ((f.ker : AddSubgroup G) : Set G)) :
      f z.anchor = f a := by
    obtain ⟨v, hv⟩ := z.active_nonempty
    have hvz := z.active_subset_coset hv
    have hva := hcontained hv
    have heq : f v = f z.anchor := by
      have hh : v ∈ z.anchor +ᵥ (f.ker : Set G) := by simpa only [hperiod] using hvz
      rwa [← addHom_fiber_eq_coset] at hh
    have heqa : f v = f a := by rwa [← addHom_fiber_eq_coset] at hva
    exact heq.symm.trans heqa
  have ha : f p.left.anchor = f b.left_anchor :=
    anchor_eq A p.left b.left_anchor
      (b.left_containment.trans inter_subset_left)
  have hb : f p.right.anchor = f b.right_anchor :=
    anchor_eq B p.right b.right_anchor (b.right_containment.trans inter_subset_left)
  have hanchor : f d.anchor = f (b.left_anchor + b.right_anchor) := by
    change f (p.left.anchor + p.right.anchor) = _
    rw [map_add, map_add, ha, hb]
  have hcomp (x : G) : naturalCyclicProjection h b.modulus
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h) x) = f x := by
    rw [hquotient]
    exact congrArg (fun k => k x) (finiteQuotient_natural_refinement U q h b.modulus hd hmh)
  have hpActive (s : ZMod (h : ℕ)) : loebResidueProfile U hU q h d.active s =
      if naturalCyclicProjection h b.modulus s = f d.anchor
        then b.left_length + b.right_length else 0 := by
    rw [hanchor]
    change loebResidueProfile U hU q h (p.left.active + p.right.active) s = _
    rw [loebResidueProfile_eq_of_ae U hU q h _ _ hsumModel]
    have hp := loeb_natural_bohr_residue_profile U hU q b.modulus h hd hmh b.character
      b.character_surjective (b.left_anchor + b.right_anchor) (b.left_start + b.right_start)
      (b.left_length + b.right_length) (add_nonneg b.left_positive.le b.right_positive.le)
      b.length_sum_lt_one.le s
    simpa only [internalBohrCoset, ← hquotient] using hp
  have hout := loeb_quasiPeriodic_refined_profile U hU q (A + B) p.period d f hperiod.symm h hd
    (naturalCyclicProjection h b.modulus) hcomp (b.left_length + b.right_length) hpActive r
  simpa only [hanchor] using hout

end Erdos335.Loeb

end
