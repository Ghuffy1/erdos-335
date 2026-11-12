import Erdos335.FinitePositiveCarrier
import Erdos335.LoebPeriodicWindowProfiles

/-!
# Literal carrier recovery and the output gap bound from positive profiles
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal BigOperators

noncomputable section

namespace Erdos335.Loeb

local instance positiveCarrierLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_window_carrier_eq_of_positive_partner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (S : Finset (ZMod (h : ℕ)))
    (hS : S ⊆ residues (h : ℕ) A)
    (hcard : (S + residues (h : ℕ) B).card + 1 = S.card + (residues (h : ℕ) B).card)
    (s t : ZMod (h : ℕ)) (hs : s ∈ S) (ht : t ∈ residues (h : ℕ) B)
    (hpositive : ∀ r ∈ residues (h : ℕ) B, 0 < actualWindowProfile U hU q h B start r)
    (hfull : ∀ r ∈ residues (h : ℕ) B, r ≠ t → actualWindowProfile U hU q h B start r = 1)
    (hzero : ∀ r ∉ S + residues (h : ℕ) B, actualWindowProfile U hU q h (A + B) start r = 0)
    (hpartial : actualWindowProfile U hU q h (A + B) start (s + t) < 1) :
    residues (h : ℕ) A = S := by
  apply FiniteProfiles.carrier_eq_of_positive_partner (residues (h : ℕ) A) S (residues (h : ℕ) B)
    (actualWindowProfile U hU q h B start) (actualWindowProfile U hU q h (A + B) start)
    hS hcard s t hs ht hpositive hfull hzero hpartial
  intro r hr v hv
  obtain ⟨n, hn, hnr⟩ := mem_residues.mp hr
  have hm := actual_window_profile_translate_le U hU q hq h hd B A start n hn v
  change actualWindowProfile U hU q h B start v ≤
    actualWindowProfile U hU q h (B + A) start (v + (n : ZMod (h : ℕ))) at hm
  simpa only [hnr, add_comm B A, add_comm v r] using hm

theorem actual_window_gamma_bound_of_critical_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (s t : ZMod (h : ℕ)) (hs : s ∈ residues (h : ℕ) A) (ht : t ∈ residues (h : ℕ) B)
    (hfullA : ∀ r ∈ (residues (h : ℕ) A).erase s, actualWindowProfile U hU q h A start r = 1)
    (hfullB : ∀ r ∈ (residues (h : ℕ) B).erase t, actualWindowProfile U hU q h B start r = 1)
    (hcard : (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
      (residues (h : ℕ) A).card + (residues (h : ℕ) B).card) :
    gamma A B ≤ a + b + (1 : ℝ) / (h : ℕ) := by
  classical
  have lower (E : Set ℕ) (d : ℝ)
      (hmE : (loebMeasure U hU (internalSet U
        (fun n => (cyclicWindow E (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = d)
      (r : ZMod (h : ℕ)) (hr : r ∈ residues (h : ℕ) E)
      (hfull : ∀ s ∈ (residues (h : ℕ) E).erase r, actualWindowProfile U hU q h E start s = 1) :
      ((residues (h : ℕ) E).card : ℝ) - 1 ≤ ((h : ℕ) : ℝ) * d := by
    have hsum : (∑ s ∈ (residues (h : ℕ) E).erase r, actualWindowProfile U hU q h E start s) =
        (((residues (h : ℕ) E).erase r).card : ℝ) := by
      simp only [Finset.sum_congr rfl hfull, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := actualWindowProfile U hU q h E start)
      (Finset.subset_univ ((residues (h : ℕ) E).erase r))
      (fun s _ _ => loebResidueProfile_nonneg U hU q h _ (s - finiteValue U (fun n => (start n : ZMod (h : ℕ)))))
    have htotal : (∑ s, actualWindowProfile U hU q h E start s) = ((h : ℕ) : ℝ) * d := by
      have hm := sum_shifted_loebResidueProfile U hU q h
        (internalSet U (fun n => (cyclicWindow E (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
        (finiteValue U (fun n => (start n : ZMod (h : ℕ))))
      simpa only [actualWindowProfile, hmE] using hm
    rw [hsum, htotal] at hle
    have hcount : ((((residues (h : ℕ) E).erase r).card : ℝ)) + 1 = (residues (h : ℕ) E).card := by
      exact_mod_cast Finset.card_erase_add_one hr
    linarith
  have hA := lower A a hmA s hs hfullA
  have hB := lower B b hmB t ht hfullB
  have hc : ((residues (h : ℕ) A + residues (h : ℕ) B).card : ℝ) + 1 =
      ((residues (h : ℕ) A).card : ℝ) + (residues (h : ℕ) B).card := by exact_mod_cast hcard
  have hbound : ((residues (h : ℕ) A + residues (h : ℕ) B).card : ℝ) ≤
      ((h : ℕ) : ℝ) * (a + b) + 1 := by nlinarith
  have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hg := gamma_le_modularCapacity A B h
  change gamma A B ≤ ((residues (h : ℕ) A + residues (h : ℕ) B).card : ℝ) / (h : ℕ) at hg
  refine hg.trans ((div_le_div_of_nonneg_right hbound hh.le).trans_eq ?_)
  field_simp

end Erdos335.Loeb

end
