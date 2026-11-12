import Erdos335.LoebPositiveCarrier
import Erdos335.LoebRegularPrefixProfiles
import Erdos335.LoebQuasiFiniteProfiles
import Erdos335.LoebShiftedWindowCores
import Erdos335.LoebQuasiPeriodicFiniteFrame
import Erdos335.LoebQuasiPeriodicActiveBounds

/-!
# An output-gap bound for a positive quasi-periodic prefix/window pair
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance regularQuasiPeriodBoundLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_regular_prefix_quasi_period_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ)
    (D : ∀ n, Set (ZMod (q n : ℕ))) (E : ℕ → Set ℕ)
    (hDsub : internalSet U D ⊆ internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hDAE : internalSet U D =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hEsub : ∀ᶠ n in U, E n ⊆ B) (hexhaust : ∀ v ∈ B, ∀ᶠ n in U, v ∈ E n)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmE : (loebMeasure U hU (internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b)
    (happroxB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) B).card : ℝ) / (k : ℕ) ≤ b + ε)
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (internalSet U D) (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hpositive : 0 < loebMeasure U hU p.right.active)
    (hfull : loebMeasure U hU
      (internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) =
        loebMeasure U hU (internalSet U D) +
          loebMeasure U hU (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hmodelC : internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hnotperiod : ¬ ∀ t ∈ p.period, t +ᵥ
      (internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))
        =ᵐ[loebMeasure U hU]
          internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))
    (h : ℕ+) (hker : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker = p.period) :
    gamma A B ≤ a + b + (1 : ℝ) / (h : ℕ) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let W := internalSet U D
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  let X := (φ '' W).toFinite.toFinset
  let T := residues (h : ℕ) B
  let S := X.image (fun r => r + z)
  let s := φ p.left.anchor + z
  let t := φ p.right.anchor
  have hX : φ '' W = (X : Set (ZMod (h : ℕ))) := by ext r; simp [X]
  have hT : φ '' P = (T : Set (ZMod (h : ℕ))) :=
    finiteQuotient_image_of_literal_exhaustion U q B E hEsub hexhaust h _
      ((hdiv h).mono fun n hn v => naturalCyclicProjection_natCast (q n) h hn v)
  have hSm : MeasurableSet (W + P) := by
    dsimp only [W, P]
    rw [← internalSet_add]
    exact measurable_internalSet U _
  have hcard0 : (X + T).card + 1 = X.card + T.card :=
    loeb_quasiPeriodic_finite_quotient_cardinality U hU q W P p hSm hfull h _
      ((hdiv h).mono fun n hn => naturalCyclicProjection_surjective (q n) h hn) hker X T hX hT
  obtain ⟨hs0, ht, _⟩ := loeb_quasiPeriodic_finite_quotient_expression U hU q W P p φ hker X T hX hT
  have hs : s ∈ S := Finset.mem_image.mpr ⟨φ p.left.anchor, hs0, rfl⟩
  have hSsub : S ⊆ residues (h : ℕ) A :=
    actual_window_core_image_subset U q h (hdiv h) A start W hDsub X hX
  have hcard : (S + T).card + 1 = S.card + T.card := by
    have htranslate : S + T = (X + T).image (fun r => r + z) := finset_translate_add X T z
    have hScard : S.card = X.card :=
      Finset.card_image_of_injective X (fun r v hrv => add_right_cancel hrv)
    rw [htranslate, Finset.card_image_of_injective _ (fun r v hrv => add_right_cancel hrv), hScard]
    exact hcard0
  have hprofileB (r : ZMod (h : ℕ)) : actualWindowProfile U hU q h B start r =
      if r = t then ((h : ℕ) : ℝ) * (μ p.right.active).toReal
      else if r ∈ T then 1 else 0 := by
    rw [← loeb_regular_prefix_profile_eq_window U hU q hdiv B E start hEsub hexhaust b hmE hmB happroxB]
    have hp := loeb_quasiPeriodic_residue_profile U hU q P p.period p.right h (hdiv h) hker r
    change loebResidueProfile U hU q h P r =
      (if r = t then ((h : ℕ) : ℝ) * (μ p.right.active).toReal
      else if r ∈ φ '' P then 1 else 0) at hp
    rw [hT] at hp
    simpa only [Finset.mem_coe] using hp
  have hpositiveB : ∀ r ∈ T, 0 < actualWindowProfile U hU q h B start r := by
    intro r hr
    rw [hprofileB]
    split_ifs
    · exact mul_pos (by exact_mod_cast h.pos)
        (ENNReal.toReal_pos hpositive.ne' (measure_ne_top μ _))
    · norm_num
  have hfullB : ∀ r ∈ T, r ≠ t → actualWindowProfile U hU q h B start r = 1 := by
    intro r hr hrt
    rw [hprofileB, if_neg hrt, if_pos hr]
  have hfullA : ∀ r ∈ S.erase s, actualWindowProfile U hU q h A start r = 1 := by
    intro r hr
    obtain ⟨hrs, hrS⟩ := Finset.mem_erase.mp hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hrS
    have hvanchor : v ≠ φ p.left.anchor := by
      intro heq
      exact hrs (congrArg (fun w => w + z) heq)
    change loebResidueProfile U hU q h _ ((v + z) - z) = 1
    rw [add_sub_cancel_right, ← loebResidueProfile_eq_of_ae U hU q h W _ hDAE]
    have hp := loeb_quasiPeriodic_residue_profile U hU q W p.period p.left h (hdiv h) hker v
    rw [if_neg hvanchor, if_pos (show v ∈ φ '' W by rw [hX]; exact hv)] at hp
    exact hp
  have hzero : ∀ r ∉ S + T, actualWindowProfile U hU q h (A + B) start r = 0 := by
    have hsumImage : φ '' (W + P) = ((X + T : Finset (ZMod (h : ℕ))) : Set (ZMod (h : ℕ))) := by
      rw [Set.image_add, hX, hT, Finset.coe_add]
    have hsub : W + P ⊆ φ ⁻¹' ((X + T : Finset (ZMod (h : ℕ))) : Set (ZMod (h : ℕ))) := by
      rw [← hsumImage]
      exact subset_preimage_image φ (W + P)
    have hz := actual_window_profile_zero_of_core U hU q h (A + B) start (W + P) hmodelC (X + T) hsub
    change ∀ r ∉ (X + T).image (fun v => v + z),
      actualWindowProfile U hU q h (A + B) start r = 0 at hz
    rw [← finset_translate_add X T z] at hz
    exact hz
  let sumDecomposition := loeb_quasiPeriodic_sum_decomposition U hU q W P p hSm
  have hactiveLt : μ sumDecomposition.active < μ (p.period : Set G) :=
    (loeb_quasiPeriodic_active_mass_bounds U hU q (W + P) (W + P) p.period sumDecomposition
      (Filter.EventuallyEq.refl _ _) hnotperiod).2
  have hHmass : (μ (p.period : Set G)).toReal = (1 : ℝ) / (h : ℕ) := by
    rw [← hker, finiteQuotient_ker, loebMeasure_internalSubgroup_of_eventually_quotients U hU
      (fun n => naturalCyclicProjection (q n) h)
      ((hdiv h).mono fun n hn => naturalCyclicProjection_surjective (q n) h hn),
      ENNReal.toReal_div]
    simp
  have hpartial : actualWindowProfile U hU q h (A + B) start (s + t) < 1 := by
    change loebResidueProfile U hU q h _ ((s + t) - z) < 1
    rw [← loebResidueProfile_eq_of_ae U hU q h (W + P) _ hmodelC]
    have hcoordinate : (s + t) - z = φ (p.left.anchor + p.right.anchor) := by
      dsimp only [s, t]
      rw [map_add]
      abel
    rw [hcoordinate]
    have hp := loeb_quasiPeriodic_residue_profile U hU q (W + P) p.period sumDecomposition h
      (hdiv h) hker (φ (p.left.anchor + p.right.anchor))
    have hanchor : φ (p.left.anchor + p.right.anchor) =
        finiteQuotient U (fun n => naturalCyclicProjection (q n) h) sumDecomposition.anchor := rfl
    rw [if_pos hanchor] at hp
    rw [hp]
    have hlt := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr hactiveLt
    rw [hHmass] at hlt
    have hm := mul_lt_mul_of_pos_left hlt (by exact_mod_cast h.pos : (0 : ℝ) < (h : ℕ))
    have hone : ((h : ℕ) : ℝ) * ((1 : ℝ) / (h : ℕ)) = 1 := by
      field_simp
    exact hm.trans_eq hone
  have hcarrier : residues (h : ℕ) A = S :=
    actual_window_carrier_eq_of_positive_partner U hU q hq h (hdiv h) A B start S hSsub hcard
      s t hs ht hpositiveB hfullB hzero hpartial
  apply actual_window_gamma_bound_of_critical_profiles U hU q h A B start a b hmA hmB s t
  · rw [hcarrier]
    exact hs
  · exact ht
  · rw [hcarrier]
    exact hfullA
  · intro r hr
    exact hfullB r (Finset.mem_erase.mp hr).2 (Finset.mem_erase.mp hr).1
  · rw [hcarrier]
    exact hcard

end Erdos335.Loeb

end
