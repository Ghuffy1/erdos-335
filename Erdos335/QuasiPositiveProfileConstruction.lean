import Erdos335.PositivePairProfiles
import Erdos335.LoebPositiveTerminalGaps

/-!
# Constructing a finite profile record from a positive quasi-periodic terminal

Private proof development. Verification status is recorded separately. Literal prefix exhaustion and the actual
moving-window subset are retained in the constructor contract.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPositiveConstructionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_local_positive_profile_of_quasi_terminal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ)
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
    (hmE : (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b)
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
    Nonempty (LocalPositiveResidueProfile d.modulus A B a b
      (fun h r => actualWindowProfile U hU q h A start r)
      (fun h r => actualWindowProfile U hU q h B (fun _ => 0) r)
      (fun h r => actualWindowProfile U hU q h (A + B) start r)) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let W := internalSet U D
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let h := d.modulus
  let φ := finiteQuotient U d.residue
  let X := (φ '' W).toFinite.toFinset
  let T := residues (h : ℕ) B
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  let S := X.image (fun r => r + z)
  let i := φ d.left_anchor + z
  let j := φ d.right_anchor
  have hX : φ '' W = (X : Set (ZMod (h : ℕ))) := by
    exact (φ '' W).toFinite.coe_toFinset.symm
  have hT : φ '' P = (T : Set (ZMod (h : ℕ))) :=
    finiteQuotient_image_of_literal_exhaustion U q B E hEsub hexhaust h d.residue
      (d.natural_residue.mono fun n hn => hn.2)
  have hφ : φ = finiteQuotient U (fun n => naturalCyclicProjection (q n) h) :=
    finiteQuotient_eq_of_eventually_natural U q h d.residue
      (fun n => naturalCyclicProjection (q n) h)
      (d.natural_residue.mono fun n hn => hn.2)
      ((hdiv h).mono fun n hn k => naturalCyclicProjection_natCast (q n) h hn k)
  have hSsub : S ⊆ residues (h : ℕ) A := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    have hs' : s ∈ φ '' W := by
      rw [hX]
      exact hs
    obtain ⟨w, hw, hws⟩ := hs'
    have hactual := actual_residue_of_internal_cyclic_window U q h (hdiv h) A start w (hDsub hw)
    rw [← hφ, hws] at hactual
    exact hactual
  have hScard : S.card = X.card :=
    Finset.card_image_of_injective X (fun _ _ heq => add_right_cancel heq)
  have hST : (X + T).image (fun r => r + z) = S + T := by
    ext r
    constructor
    · intro hr
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨x, hx, t, ht, rfl⟩ := Finset.mem_add.mp hv
      exact Finset.mem_add.mpr ⟨x + z, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        t, ht, by abel⟩
    · intro hr
      obtain ⟨s, hs, t, ht, rfl⟩ := Finset.mem_add.mp hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_image.mpr ⟨x + t, Finset.add_mem_add hx ht, by abel⟩
  have hsumImage : φ '' (W + P) = ((X + T : Finset (ZMod (h : ℕ))) : Set _) := by
    rw [Set.image_add, hX, hT, Finset.coe_add]
  have hSm : MeasurableSet (W + P) := by
    dsimp only [W, P]
    rw [← internalSet_add]
    exact measurable_internalSet U _
  have hcardRaw := loeb_quasiPeriodic_finite_quotient_cardinality U hU q W P p hSm hfull
    h d.residue (d.natural_residue.mono fun n hn => hn.1) hperiod.symm X T hX hT
  have hSTcard : (S + T).card = (X + T).card := by
    rw [← hST]
    exact Finset.card_image_of_injective (X + T) (fun _ _ heq => add_right_cancel heq)
  have hleftAnchor : φ p.left.anchor = φ d.left_anchor := by
    obtain ⟨w, hw⟩ := p.left.active_nonempty
    have hpa : w ∈ p.left.anchor +ᵥ (φ.ker : Set G) := by
      simpa only [hperiod] using p.left.active_subset_coset hw
    have hpa' : φ w = φ p.left.anchor := by
      rwa [← addHom_fiber_eq_coset] at hpa
    have hda : φ w = φ d.left_anchor := by
      have hdc := (d.left_containment hw).1
      rwa [← addHom_fiber_eq_coset] at hdc
    exact hpa'.symm.trans hda
  have hrightAnchor : φ p.right.anchor = φ d.right_anchor := by
    obtain ⟨w, hw⟩ := p.right.active_nonempty
    have hpa : w ∈ p.right.anchor +ᵥ (φ.ker : Set G) := by
      simpa only [hperiod] using p.right.active_subset_coset hw
    have hpa' : φ w = φ p.right.anchor := by
      rwa [← addHom_fiber_eq_coset] at hpa
    have hda : φ w = φ d.right_anchor := by
      have hdc := (d.right_containment hw).1
      rwa [← addHom_fiber_eq_coset] at hdc
    exact hpa'.symm.trans hda
  have hexpression := loeb_quasiPeriodic_finite_quotient_expression U hU q W P p φ
    hperiod.symm X T hX hT
  rw [hleftAnchor, hrightAnchor] at hexpression
  have hi : i ∈ S := Finset.mem_image.mpr ⟨φ d.left_anchor, hexpression.1, rfl⟩
  have hj : j ∈ T := hexpression.2.1
  have hunique : ∀ r ∈ S, ∀ t ∈ T, r + t = i + j → r = i ∧ t = j := by
    intro r hr t ht hrs
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    have hraw : s + t = φ d.left_anchor + φ d.right_anchor := by
      have hwith : (s + t) + z = (φ d.left_anchor + φ d.right_anchor) + z := by
        calc
          (s + t) + z = (s + z) + t := by abel
          _ = i + j := hrs
          _ = (φ d.left_anchor + φ d.right_anchor) + z := by dsimp only [i, j]; abel
      exact add_right_cancel hwith
    obtain ⟨hs', ht'⟩ := hexpression.2.2 s hs t ht hraw
    exact ⟨by simpa only [i, hs'], ht'⟩
  have hmW : (loebMeasure U hU W).toReal = a :=
    (congrArg ENNReal.toReal (measure_congr hDAE)).trans hmA
  have hmassA : a = ((X.card : ℝ) - 1 + d.left_length) / (h : ℕ) :=
    hmW.symm.trans (loeb_quasiBohr_right_mass U hU q P W p.swap d.swap hperiod (hdiv h) X hX)
  have hmassB : b = ((T.card : ℝ) - 1 + d.right_length) / (h : ℕ) :=
    hmE.symm.trans (loeb_quasiBohr_right_mass U hU q W P p d hperiod (hdiv h) T hT)
  have hnonzero : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  have htotalA : (h : ℕ) * a = (S.card : ℝ) - 1 + d.left_length := by
    rw [hScard]
    simpa only [mul_comm] using (eq_div_iff hnonzero).mp hmassA
  have htotalB : (h : ℕ) * b = (T.card : ℝ) - 1 + d.right_length := by
    simpa only [mul_comm] using (eq_div_iff hnonzero).mp hmassB
  have houtputAnchor : φ (d.left_anchor + d.right_anchor) + z = i + j := by
    dsimp only [i, j]
    rw [map_add]
    abel
  refine ⟨{
    movingSupport := S
    support_subset := hSsub
    activeMoving := i
    activePrefix := j
    activeMoving_mem := hi
    activePrefix_mem := hj
    movingMass := d.left_length
    prefixMass := d.right_length
    moving_positive := d.left_positive
    prefix_positive := d.right_positive
    mass_sum_lt_one := d.length_sum_lt_one
    total_moving := htotalA
    total_prefix := htotalB
    cardinality := by
      change (S + T).card + 1 = S.card + T.card
      rw [hSTcard, hScard]
      exact hcardRaw
    unique_expression := hunique
    moving_profile := ?_
    prefix_profile := ?_
    output_profile := ?_
  }⟩
  · intro m hm r
    exact loeb_physical_bohr_left_profile U hU q W P p d hperiod A start hDAE X hX m (hdiv m) hm r
  · intro m hm r
    have hp := loeb_physical_bohr_right_profile U hU q W P p d hperiod B (fun _ => 0) hP0
      T hT m (hdiv m) hm r
    simpa only [positiveResiduePattern, Nat.cast_zero, finiteValue_const, add_zero, Finset.image_id'] using hp
  · intro m hm r
    have hp := loeb_physical_bohr_output_profile U hU q W P p hSm d hperiod (A + B) start hmodelC
      (X + T) hsumImage m (hdiv m) hm r
    rw [hST, houtputAnchor] at hp
    exact hp

end Erdos335.Loeb

end
