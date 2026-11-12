import Erdos335.LoebPhysicalBohrInputs
import Erdos335.LoebPhysicalBohrOutput
import Erdos335.LoebPositiveOutputCarrier
import Erdos335.LoebShiftedWindowCores
import Erdos335.LoebQuasiPeriodicFiniteFrame

/-!
# Literal capacity gaps of a positive terminal
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal Classical

noncomputable section

namespace Erdos335.Loeb

local instance positiveTerminalGapsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_positive_terminal_gap_formulas
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ)
    (D : ∀ n, Set (ZMod (q n : ℕ))) (E : ℕ → Set ℕ)
    (hDAE : internalSet U D =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hEsub : ∀ᶠ n in U, E n ⊆ B) (hexhaust : ∀ v ∈ B, ∀ᶠ n in U, v ∈ E n)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmE : (loebMeasure U hU (internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b)
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (internalSet U D) (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (d : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U d.residue).ker)
    (hfull : loebMeasure U hU
      (internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) =
        loebMeasure U hU (internalSet U D) +
          loebMeasure U hU (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hmodelC : internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    gamma A B - (a + b) = (1 - d.left_length - d.right_length) / (d.modulus : ℕ) ∧
    (∀ k : ℕ+, a + (1 - d.left_length) / (d.modulus : ℕ) ≤
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ)) ∧
    (∀ k : ℕ+, b + (1 - d.right_length) / (d.modulus : ℕ) ≤
      ((residues (k : ℕ) B).card : ℝ) / (k : ℕ)) ∧
    ((residues (d.modulus : ℕ) B).card : ℝ) / (d.modulus : ℕ) =
      b + (1 - d.right_length) / (d.modulus : ℕ) := by
  let W := internalSet U D
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let m := d.modulus
  let φ := finiteQuotient U d.residue
  let X := (φ '' W).toFinite.toFinset
  let T := residues (m : ℕ) B
  let z := finiteValue U (fun n => (start n : ZMod (m : ℕ)))
  let S := X.image (fun r => r + z)
  let R := (X + T).image (fun r => r + z)
  let u := φ (d.left_anchor + d.right_anchor) + z
  have hX : φ '' W = (X : Set _) := by ext r; simp [X]
  have hT : φ '' P = (T : Set _) := finiteQuotient_image_of_literal_exhaustion U q B E
    hEsub hexhaust m d.residue (d.natural_residue.mono fun _ hn => hn.2)
  have hsum : φ '' (W + P) = ((X + T : Finset (ZMod (m : ℕ))) : Set _) := by
    rw [Set.image_add, hX, hT, Finset.coe_add]
  have hSm : MeasurableSet (W + P) := by
    dsimp only [W, P]
    rw [← internalSet_add]
    exact measurable_internalSet U _
  have hcard : (X + T).card + 1 = X.card + T.card :=
    loeb_quasiPeriodic_finite_quotient_cardinality U hU q W P p hSm hfull m d.residue
      (d.natural_residue.mono fun _ hn => hn.1) hperiod.symm X T hX hT
  have hScard : S.card = X.card :=
    Finset.card_image_of_injective X (fun _ _ heq => add_right_cancel heq)
  have hRcard : R.card = (X + T).card :=
    Finset.card_image_of_injective (X + T) (fun _ _ heq => add_right_cancel heq)
  have ha : a = ((X.card : ℝ) - 1 + d.left_length) / (m : ℕ) := by
    have hmW := (congrArg ENNReal.toReal (measure_congr hDAE)).trans hmA
    exact hmW.symm.trans (loeb_quasiBohr_right_mass U hU q P W p.swap d.swap hperiod
      (hdiv m) X hX)
  have hb : b = ((T.card : ℝ) - 1 + d.right_length) / (m : ℕ) :=
    hmE.symm.trans (loeb_quasiBohr_right_mass U hU q W P p d hperiod (hdiv m) T hT)
  have hApositive (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) (r : ZMod (h : ℕ))
      (hr : naturalCyclicProjection h m r ∈ S) : 0 < actualWindowProfile U hU q h A start r := by
    rw [loeb_physical_bohr_left_profile U hU q W P p d hperiod A start hDAE X hX h (hdiv h) hmh r]
    split_ifs
    · exact d.left_positive
    · norm_num
  have hAcap := actual_window_capacity_ge_of_positive_refinements U hU q hdiv A start m S hApositive
  have hBpositive (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) (r : ZMod (h : ℕ))
      (hr : naturalCyclicProjection h m r ∈ T) : 0 < loebResidueProfile U hU q h P r := by
    rw [loeb_quasiBohr_right_residue_profile U hU q W P p d hperiod h (hdiv h) hmh r]
    by_cases heq : naturalCyclicProjection h m r = φ d.right_anchor
    · rw [if_pos heq]
      exact d.right_positive
    · rw [if_neg heq, hT]
      simp only [Finset.mem_coe]
      split_ifs with hmem
      · norm_num
      · exact False.elim (hmem hr)
  have hBcap := literal_prefix_capacity_ge_of_positive_refinements U hU q hdiv B E hEsub hexhaust m T hBpositive
  have hCprofile (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) (r : ZMod (h : ℕ)) :
      actualWindowProfile U hU q h (A + B) start r =
        if naturalCyclicProjection h m r = u then d.left_length + d.right_length
        else if naturalCyclicProjection h m r ∈ R then 1 else 0 :=
    loeb_physical_bohr_output_profile U hU q W P p hSm d hperiod (A + B) start hmodelC
      (X + T) hsum h (hdiv h) hmh r
  have hCpositive (h : ℕ+) (hmh : (m : ℕ) ∣ (h : ℕ)) (r : ZMod (h : ℕ))
      (hr : naturalCyclicProjection h m r ∈ R) : 0 < actualWindowProfile U hU q h (A + B) start r := by
    rw [hCprofile h hmh r]
    split_ifs
    · exact add_pos d.left_positive d.right_positive
    · norm_num
  have hu : u ∈ R := by
    obtain ⟨x, hx⟩ := p.left.active_nonempty
    obtain ⟨y, hy⟩ := p.right.active_nonempty
    have hxW : x ∈ W := (subset_union_right.trans p.left.partition.ge) hx
    have hyP : y ∈ P := (subset_union_right.trans p.right.partition.ge) hy
    have hφx : φ x = φ d.left_anchor := by
      have hc := (d.left_containment hx).1
      rwa [← addHom_fiber_eq_coset] at hc
    have hφy : φ y = φ d.right_anchor := by
      have hc := (d.right_containment hy).1
      rwa [← addHom_fiber_eq_coset] at hc
    have hxX : φ x ∈ X := by rw [← Finset.mem_coe, ← hX]; exact ⟨x, hxW, rfl⟩
    have hyT : φ y ∈ T := by rw [← Finset.mem_coe, ← hT]; exact ⟨y, hyP, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨φ x + φ y, Finset.add_mem_add hxX hyT, ?_⟩
    simp only [u, map_add, hφx, hφy]
  have hid : naturalCyclicProjection m m = AddMonoidHom.id (ZMod (m : ℕ)) := by
    ext r
    rw [naturalCyclicProjection_val m m dvd_rfl, ZMod.natCast_zmod_val]
    rfl
  have hCzero (r : ZMod (m : ℕ)) (hr : r ∉ R) : actualWindowProfile U hU q m (A + B) start r = 0 := by
    have hne : r ≠ u := fun heq => hr (heq ▸ hu)
    simpa only [hid, AddMonoidHom.id_apply, if_neg hne, if_neg hr] using hCprofile m dvd_rfl r
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hmy : ((m : ℕ) : ℝ) * b - ((T.card : ℝ) - 1) = d.right_length := by
    rw [hb]
    field_simp
    ring
  have hpartner (r : ZMod (m : ℕ)) (hr : r ∈ residues (m : ℕ) B) :
      0 < actualWindowProfile U hU q m B start r := by
    have hlower := actual_window_profile_ge_total_sub_card U hU q m (hdiv m) B start b hmB r hr
    change ((m : ℕ) : ℝ) * b - ((T.card : ℝ) - 1) ≤ _ at hlower
    rw [hmy] at hlower
    exact d.right_positive.trans_le hlower
  have hcarrier := actual_output_literal_carrier U hU q hq m (hdiv m) A B start R hpartner hCzero
    (fun r hr => hCpositive m dvd_rfl r (by simpa only [hid, AddMonoidHom.id_apply] using hr))
  have hgamma := gamma_eq_of_positive_window_refinements U hU q hdiv A B start m R hcarrier hCpositive
  have hcardReal : ((X + T).card : ℝ) + 1 = (X.card : ℝ) + T.card := by exact_mod_cast hcard
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hgamma, hRcard, ha, hb]
    field_simp
    nlinarith
  · intro k
    have hk := hAcap k
    rw [hScard] at hk
    convert hk using 1 <;> rw [ha] <;> ring
  · intro k
    convert hBcap k using 1 <;> rw [hb] <;> ring
  · change (T.card : ℝ) / (m : ℕ) = _
    rw [hb]
    ring

end Erdos335.Loeb

end
