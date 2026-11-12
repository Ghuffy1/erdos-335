import Erdos335.PositivePairProfiles
import Erdos335.LoebWholeBohrGap

/-!
# Constructing a finite profile record from a whole positive Bohr pair

Private proof development. Verification status is recorded separately. Singleton supports give the empty-background
case directly in LocalPositiveResidueProfile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance wholePositiveConstructionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_local_positive_profile_of_whole_bohr
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (hB : B.Nonempty) (start : ℕ → ℕ) (a b : ℝ) (hb : 0 < b)
    (D : ∀ n, Set (ZMod (q n : ℕ))) (E : ℕ → Set ℕ)
    (hDsub : internalSet U D ⊆ internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hDAE : internalSet U D =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hEsub : ∀ᶠ n in U, E n ⊆ B) (hexhaust : ∀ v ∈ B, ∀ᶠ n in U, v ∈ E n)
    (hP0 : internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmE : (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b)
    (d : InternalBohrPairData U hU q (internalSet U D)
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hfull : loebMeasure U hU
      (internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) =
        loebMeasure U hU (internalSet U D) +
          loebMeasure U hU (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hmodelC : internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    Nonempty (LocalPositiveResidueProfile d.modulus A B a b
      (fun h r => actualWindowProfile U hU q h A start r)
      (fun h r => actualWindowProfile U hU q h B (fun _ => 0) r)
      (fun h r => actualWindowProfile U hU q h (A + B) start r)) := by
  classical
  letI : IsProbabilityMeasure (loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU) :=
    isProbabilityMeasure_loebMeasure U hU
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let W := internalSet U D
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let h := d.modulus
  let φ := finiteQuotient U d.residue
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  let i := φ d.left_anchor + z
  let j := φ d.right_anchor
  let S : Finset (ZMod (h : ℕ)) := {i}
  have hSm : MeasurableSet (W + P) := by
    dsimp only [W, P]
    rw [← internalSet_add]
    exact measurable_internalSet U _
  obtain ⟨hmassA, hmassB, _, _, _⟩ := whole_bohr_gap_formulas U hU q hdiv hq
    A B hB start a b hb W E hDAE hEsub hexhaust hmA hmB hmE d hSm hfull hmodelC
  have hRB : residues (h : ℕ) B = {j} :=
    whole_bohr_prefix_carrier U hU q W B E hB hEsub hexhaust d
  have hφ : φ = finiteQuotient U (fun n => naturalCyclicProjection (q n) h) :=
    finiteQuotient_eq_of_eventually_natural U q h d.residue
      (fun n => naturalCyclicProjection (q n) h)
      (d.natural_residue.mono fun n hn => hn.2)
      ((hdiv h).mono fun n hn k => naturalCyclicProjection_natCast (q n) h hn k)
  have hWmass : (loebMeasure U hU W).toReal = a :=
    (congrArg ENNReal.toReal (measure_congr hDAE)).trans hmA
  have ha : 0 < a := by
    rw [hmassA]
    exact div_pos d.left_positive (by exact_mod_cast h.pos)
  have hWpos : 0 < loebMeasure U hU W :=
    (ENNReal.toReal_pos_iff.mp (by rw [hWmass]; exact ha)).1
  obtain ⟨w, hw⟩ := nonempty_of_measure_ne_zero hWpos.ne'
  have hwi : φ w = φ d.left_anchor := by
    have hc := (d.left_containment hw).1
    rwa [← addHom_fiber_eq_coset] at hc
  have hiA : i ∈ residues (h : ℕ) A := by
    have hactual := actual_residue_of_internal_cyclic_window U q h (hdiv h) A start w (hDsub hw)
    rw [← hφ, hwi] at hactual
    exact hactual
  have hSsub : S ⊆ residues (h : ℕ) A := by
    intro r hr
    have hr' : r = i := Finset.mem_singleton.mp hr
    exact hr'.symm ▸ hiA
  have hnonzero : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  have htotalA : (h : ℕ) * a = (S.card : ℝ) - 1 + d.left_length := by
    simp only [S, Finset.card_singleton, Nat.cast_one, sub_self, zero_add]
    simpa only [mul_comm] using (eq_div_iff hnonzero).mp hmassA
  have htotalB : (h : ℕ) * b = ((residues (h : ℕ) B).card : ℝ) - 1 + d.right_length := by
    rw [hRB]
    simp only [Finset.card_singleton, Nat.cast_one, sub_self, zero_add]
    simpa only [mul_comm] using (eq_div_iff hnonzero).mp hmassB
  have houtputAnchor : φ (d.left_anchor + d.right_anchor) + z = i + j := by
    dsimp only [i, j]
    rw [map_add]
    abel
  change Nonempty (LocalPositiveResidueProfile h A B a b _ _ _)
  refine ⟨{
    movingSupport := S
    support_subset := hSsub
    activeMoving := i
    activePrefix := j
    activeMoving_mem := Finset.mem_singleton_self i
    activePrefix_mem := by rw [hRB]; exact Finset.mem_singleton_self j
    movingMass := d.left_length
    prefixMass := d.right_length
    moving_positive := d.left_positive
    prefix_positive := d.right_positive
    mass_sum_lt_one := d.length_sum_lt_one
    total_moving := htotalA
    total_prefix := htotalB
    cardinality := by simp only [S, hRB, Finset.singleton_add_singleton, Finset.card_singleton]
    unique_expression := ?_
    moving_profile := ?_
    prefix_profile := ?_
    output_profile := ?_
  }⟩
  · intro r hr t ht _
    exact ⟨Finset.mem_singleton.mp hr, by rw [hRB] at ht; exact Finset.mem_singleton.mp ht⟩
  · intro m hm r
    have hp := whole_bohr_left_physical_profile U hU q W P d A start hDAE m (hdiv m) hm r
    change actualWindowProfile U hU q m A start r =
      (if naturalCyclicProjection m h r = i then d.left_length else 0) at hp
    rw [hp]
    by_cases hr : naturalCyclicProjection m h r = i <;>
      simp only [positiveResiduePattern, S, Finset.mem_singleton, hr, ite_true, ite_false]
  · intro m hm r
    have hp := whole_bohr_right_physical_profile U hU q W P d B (fun _ => 0) hP0 m (hdiv m) hm r
    simp only [Nat.cast_zero, finiteValue_const, add_zero] at hp
    change actualWindowProfile U hU q m B (fun _ => 0) r =
      (if naturalCyclicProjection m h r = j then d.right_length else 0) at hp
    rw [hp]
    by_cases hr : naturalCyclicProjection m h r = j <;>
      simp only [positiveResiduePattern, hRB, Finset.mem_singleton, hr, ite_true, ite_false]
  · intro m hm r
    have hp := whole_bohr_output_physical_profile U hU q W P d hSm hfull (A + B) start hmodelC
      m (hdiv m) hm r
    rw [houtputAnchor] at hp
    change actualWindowProfile U hU q m (A + B) start r =
      (if naturalCyclicProjection m h r = i + j then d.left_length + d.right_length else 0) at hp
    rw [hp]
    by_cases hr : naturalCyclicProjection m h r = i + j <;>
      simp only [positiveResiduePattern, S, hRB, Finset.singleton_add_singleton,
        Finset.mem_singleton, hr, ite_true, ite_false]

end Erdos335.Loeb

end
