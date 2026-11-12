import Erdos335.OrdinaryDensityPrefixModel
import Erdos335.LoebHighGapTerminal
import Erdos335.UniformPrefixWholeBohr
import Erdos335.LoebGlobalPrefixArc
import Erdos335.OrdinaryArcCompanion
import Erdos335.LoebBohrSumModel

/-!
# The inverse theorem for ordinary uniform residue densities

Private proof development. Verification status is recorded separately.
The local models are constructed from the given ordinary densities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Proposed

local instance uniformResidueInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := Loeb.loebMeasurableSpace U

theorem full_support_of_uniform_residue_densities
    (A : Set ℕ) (a : ℝ) (ha : 0 < a)
    (hdens : ∀ h : ℕ+, ∀ r : ZMod (h : ℕ),
      HasDensity (residueFiber A r) (a / (h : ℕ))) :
    ∀ h : ℕ+, residues (h : ℕ) A = Finset.univ := by
  classical
  intro h
  apply Finset.eq_univ_of_forall
  intro r
  apply positiveResidues_subset_residues (h : ℕ) A
  rw [mem_positiveResidues]
  intro hzero
  have heq : a / (h : ℕ) = 0 := (hdens h r).unique hzero
  have hpositive : 0 < a / (h : ℕ) := div_pos ha (by exact_mod_cast h.pos)
  exact hpositive.ne' heq

theorem gamma_eq_one_of_full_support
    (A B : Set ℕ)
    (hA : ∀ h : ℕ+, residues (h : ℕ) A = Finset.univ)
    (hB : ∀ h : ℕ+, residues (h : ℕ) B = Finset.univ) :
    gamma A B = 1 := by
  classical
  have hcapacity (h : ℕ+) : modularCapacity A B h = 1 := by
    have hsum : (Finset.univ + Finset.univ : Finset (ZMod (h : ℕ))) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro r
      exact Finset.mem_add.mpr ⟨0, Finset.mem_univ _, r, Finset.mem_univ _, zero_add r⟩
    rw [modularCapacity, hA h, hB h, hsum, Finset.card_univ, ZMod.card]
    exact div_self (by exact_mod_cast h.ne_zero)
  simp only [gamma, hcapacity, ciInf_const]

theorem positive_multiples_density_of_uniform_residue_densities
    (A : Set ℕ) (hA : A ⊆ Ioi 0) (a : ℝ) (ha : 0 < a)
    (hdens : ∀ h : ℕ+, ∀ r : ZMod (h : ℕ),
      HasDensity (residueFiber A r) (a / (h : ℕ))) :
    ∀ h : ℕ+, ∃ ρ : ℝ, 0 < ρ ∧ HasDensity (A ∩ {n : ℕ | (h : ℕ) ∣ n}) ρ := by
  intro h
  have heq : residueFiber A (0 : ZMod (h : ℕ)) = A ∩ {n : ℕ | (h : ℕ) ∣ n} := by
    ext n
    change (n ∈ A ∧ 0 < n ∧ (n : ZMod (h : ℕ)) ∈ ({0} : Finset (ZMod (h : ℕ)))) ↔
      n ∈ A ∧ (h : ℕ) ∣ n
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨hn, _, hr⟩
      exact ⟨hn, (ZMod.natCast_eq_zero_iff n (h : ℕ)).mp hr⟩
    · rintro ⟨hn, hd⟩
      exact ⟨hn, hA hn, (ZMod.natCast_eq_zero_iff n (h : ℕ)).mpr hd⟩
  exact ⟨a / (h : ℕ), div_pos ha (by exact_mod_cast h.pos), by
    simpa only [heq] using hdens h 0⟩

theorem parallel_irrational_arcs_of_uniform_residue_densities
    (A B : Set ℕ) (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (hAres : ∀ h : ℕ+, ∀ r : ZMod (h : ℕ),
      HasDensity (residueFiber A r) (a / (h : ℕ)))
    (hBres : ∀ h : ℕ+, ∀ r : ZMod (h : ℕ),
      HasDensity (residueFiber B r) (b / (h : ℕ))) :
    ∃ θ startA startB : ℝ, Irrational θ ∧
      A ⊆ closedArcPullback θ startA a ∧ B ⊆ closedArcPullback θ startB b ∧
      HasDensity (closedArcPullback θ startA a \ A) 0 ∧
      HasDensity (closedArcPullback θ startB b \ B) 0 := by
  classical
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨q, start, D, E, hdiv, hq, hDsub, hDAE, hEsub, hexhaust, hprefix,
      hmA, hmB, hmC, hmE, hsum⟩ :=
    exists_ordinary_density_loeb_models_with_prefix U hU A B a b (a + b) hA hB hC
  let W := Loeb.internalSet U D
  let P := Loeb.internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let μ := Loeb.loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hAfull := full_support_of_uniform_residue_densities A a ha hAres
  have hBfull := full_support_of_uniform_residue_densities B b hb hBres
  have hgamma : gamma A B = 1 := gamma_eq_one_of_full_support A B hAfull hBfull
  have hcapA (h : ℕ+) : a + (1 - a) ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
    rw [hAfull h, Finset.card_univ, ZMod.card, div_self (by exact_mod_cast h.ne_zero)]
    linarith
  have hcapB (h : ℕ+) : b + (1 - b) ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ) := by
    rw [hBfull h, Finset.card_univ, ZMod.card, div_self (by exact_mod_cast h.ne_zero)]
    linarith
  obtain ⟨_, _, hterminal⟩ := Loeb.loeb_high_gap_positive_terminal U hU q hdiv hq
    A B start a b (1 - a) (1 - b) ha hb hA hB hC
    (by rw [hgamma]; exact hab) (by rw [hgamma]; linarith)
    (by rw [hgamma]; linarith) hcapA hcapB D E hDsub hDAE hEsub hexhaust hprefix
    hmA hmB hmC hmE hsum
  obtain ⟨d, hdmod⟩ := Loeb.whole_bohr_of_uniform_prefix_terminal U hU q hq hdiv
    B hBpos b hb (by linarith) hBres W P hprefix hterminal
  have hdmodNat : (d.modulus : ℕ) = 1 := congrArg Subtype.val hdmod
  have hlengthMeasure := Loeb.internalBohrCoset_measure_toReal U hU q d.modulus (hdiv d.modulus)
    d.residue (d.natural_residue.mono fun n hn => hn.2) d.character d.character_surjective
    d.right_anchor d.right_start d.right_length d.right_positive.le
    (by linarith [d.length_sum_lt_one, d.left_positive])
  have hlength : d.right_length = b := by
    have hm : (μ (Loeb.internalBohrCoset U q d.modulus d.residue d.character
        d.right_anchor d.right_start d.right_length)).toReal = b :=
      (congrArg ENNReal.toReal (measure_congr d.right_model)).symm.trans hmE
    rw [hlengthMeasure, hdmodNat, Nat.cast_one, div_one] at hm
    exact hm
  letI : Subsingleton (ZMod (d.modulus : ℕ)) := by rw [hdmodNat]; infer_instance
  have hcoset : d.right_anchor +ᵥ ((Loeb.finiteQuotient U d.residue).ker :
      Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) = univ := by
    apply eq_univ_of_forall
    intro g
    refine ⟨g - d.right_anchor, ?_, by change d.right_anchor + (g - d.right_anchor) = g; abel⟩
    change Loeb.finiteQuotient U d.residue (g - d.right_anchor) = 0
    exact Subsingleton.elim _ _
  have hmodel : P =ᵐ[μ] (Loeb.ultralimitAddHom U d.character) ⁻¹'
      (d.right_start +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b)) := by
    simpa only [Loeb.internalBohrCoset, hcoset, univ_inter, hlength] using d.right_model
  have hcontain : P ⊆ (Loeb.ultralimitAddHom U d.character) ⁻¹'
      (d.right_start +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b)) := by
    intro z hz
    simpa only [hlength] using (d.right_containment hz).2
  have hAmultiples := positive_multiples_density_of_uniform_residue_densities A hApos a ha hAres
  have hBmultiples := positive_multiples_density_of_uniform_residue_densities B hBpos b hb hBres
  obtain ⟨θ, startB, hθ, hBsub, hBholes⟩ := Loeb.global_prefix_irrational_arc U hU q hq hdiv
    A B (a + b) b hC hab hBpos hB hb (by linarith) hAmultiples hBmultiples
    d.character d.character_surjective E hexhaust d.right_start hcontain hprefix hmodel
  obtain ⟨startA, hAsub, hAholes⟩ := ordinary_filled_arc_companion U hU q
    (Loeb.ultralimitAddHom U d.character) (Loeb.measurable_ultralimitAddHom U d.character)
    d.character_surjective θ startB a b hθ A B hApos ha hb hab hA hC hBsub hBholes
  exact ⟨θ, startA, startB, hθ, hAsub, hBsub, hAholes, hBholes⟩

end Erdos335.Proposed

end
