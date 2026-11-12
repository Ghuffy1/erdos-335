import Erdos335.LoebSubcriticalQuotientCore
import Erdos335.LoebLocalDeficitProfiles
import Erdos335.LoebShiftedWindowCores
import Erdos335.LoebShiftedProfileMasks

/-!
# A strict cyclic-model deficit forces a periodic actual input window
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal BigOperators

noncomputable section

namespace Erdos335.Loeb

local instance subcriticalWindowCompensationLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem subcritical_window_is_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun s => (q s : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
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
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hmE : (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b)
    (hsum : internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      ≤ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hsmall : loebMeasure U hU
      (internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) <
        loebMeasure U hU (internalSet U D) +
          loebMeasure U hU (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hgap : a + b < gamma A B) :
    ∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))),
      (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      (internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) ∧
      a = (R.card : ℝ) / (h : ℕ) := by
  classical
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let F := fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n
  have hmD : (μ (internalSet U D)).toReal = a :=
    (congrArg ENNReal.toReal (measure_congr hDAE)).trans hmA
  have hDpos : 0 < μ (internalSet U D) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    rw [hz, ENNReal.toReal_zero] at hmD
    linarith
  have hEpos : 0 < μ (internalSet U F) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    change (μ (internalSet U F)).toReal = b at hmE
    rw [hz, ENNReal.toReal_zero] at hmE
    linarith
  have hsmall' : μ (internalSet U (fun n => D n + F n)) <
      μ (internalSet U D) + μ (internalSet U F) := by
    rw [internalSet_add]
    exact hsmall
  obtain ⟨h, S₀, T, hd, hS₀, hT, hcore, hcard₀⟩ :=
    exists_loeb_subcritical_quotient_core U hU q D F
      (nonempty_of_measure_ne_zero hDpos.ne') (nonempty_of_measure_ne_zero hEpos.ne') hsmall'
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  let z := finiteValue U (fun n => (start n : ZMod (h : ℕ)))
  have hTliteral := finiteQuotient_image_of_literal_exhaustion U q B E hEsub hexhaust h
    (fun n => naturalCyclicProjection (q n) h)
    (hd.mono fun n hn t => naturalCyclicProjection_natCast (q n) h hn t)
  have hTeq : T = residues (h : ℕ) B := Finset.coe_injective (hT.symm.trans hTliteral)
  subst T
  let S := S₀.image (fun r => r + z)
  have hshift (V : Finset (ZMod (h : ℕ))) : (V.image (fun r => r + z)).card = V.card :=
    Finset.card_image_of_injective V (fun x y hxy => add_right_cancel hxy)
  have hSsub : S ⊆ residues (h : ℕ) A :=
    actual_window_core_image_subset U q h hd A start (internalSet U D) hDsub S₀ hS₀
  have hDmask : internalSet U D ⊆ φ ⁻¹' (S₀ : Set _) := by
    rw [← hS₀]
    exact subset_preimage_image φ (internalSet U D)
  have hzero := actual_window_profile_zero_of_core U hU q h A start (internalSet U D) hDAE S₀ hDmask
  have hcoreAE : φ ⁻¹' (S₀ + residues (h : ℕ) B : Finset _) ≤ᵐ[μ]
      internalSet U (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
    rw [← hcore, internalSet_add]
    exact hsum
  have hfull₀ := actual_window_profile_full_of_core U hU q h hd (A + B) start
    (S₀ + residues (h : ℕ) B) hcoreAE
  have hfull : ∀ r ∈ S + residues (h : ℕ) B, actualWindowProfile U hU q h (A + B) start r = 1 := by
    simpa only [S, finset_translate_add] using hfull₀
  have hcard : (S + residues (h : ℕ) B).card + 1 = S.card + (residues (h : ℕ) B).card := by
    dsimp only [S]
    rw [finset_translate_add, hshift, hshift]
    exact hcard₀
  have hcoreMass : (μ (internalSet U (fun n => D n + F n))).toReal =
      ((S₀ + residues (h : ℕ) B).card : ℝ) / (h : ℕ) := by
    rw [hcore, loebMeasure_naturalCyclicProjection_preimage U hU q h hd]
    simp
  have hsmallReal := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by finiteness)).mpr hsmall'
  rw [hcoreMass, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hmD, hmE] at hsmallReal
  have hhpos : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hdeficit : ((S + residues (h : ℕ) B).card : ℝ) < ((h : ℕ) : ℝ) * (a + b) := by
    dsimp only [S]
    rw [finset_translate_add, hshift]
    have ht := (div_lt_iff₀ hhpos).mp hsmallReal
    simpa only [mul_comm] using ht
  obtain ⟨r, t, hr, ht, hrs, hR, hdiff, hffull, hgfull, hgt, hgt1, huniq⟩ :=
    actual_window_local_deficit_template U hU q hq h hd A B start a b hmA hmB hmC hgap S hSsub
      hcard hzero hfull hdeficit
  have hindicator : ∀ r, actualWindowProfile U hU q h A start r = if r ∈ S then (1 : ℝ) else 0 := by
    intro r
    by_cases hr : r ∈ S
    · simpa only [if_pos hr] using hffull r hr
    · simpa only [if_neg hr] using hzero r hr
  let R := S.image (fun r => r - z)
  have hAE := loeb_ae_eq_shifted_mask_of_full_profile U hU q h hd _ (measurable_internalSet U _)
    S z hindicator
  refine ⟨h, R, hd, hAE, ?_⟩
  have hm := congrArg ENNReal.toReal (measure_congr hAE)
  rw [hmA, loebMeasure_naturalCyclicProjection_preimage U hU q h hd] at hm
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast] using hm

end Erdos335.Loeb

end
