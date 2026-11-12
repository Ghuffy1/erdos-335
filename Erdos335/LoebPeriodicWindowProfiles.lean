import Erdos335.LoebWindowTranslations
import Erdos335.FiniteProfileSupport
import Erdos335.PeriodicOutput

/-!
# A periodic output profile forces full input profiles
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped BigOperators ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance periodicWindowProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

def actualWindowProfile (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (q : ℕ → ℕ+) (h : ℕ+) (A : Set ℕ) (start : ℕ → ℕ) (r : ZMod (h : ℕ)) : ℝ :=
  loebResidueProfile U hU q h
    (internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (r - finiteValue U (fun n => (start n : ZMod (h : ℕ))))

theorem periodic_output_window_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun s => (q s : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (R : Finset (ZMod (h : ℕ)))
    (hR : ∀ r, actualWindowProfile U hU q h (A + B) start r = if r ∈ R then (1 : ℝ) else 0) :
    ∃ P Q : Finset (ZMod (h : ℕ)), P ⊆ residues (h : ℕ) A ∧ Q ⊆ residues (h : ℕ) B ∧
      R.card = P.card + Q.card ∧
      (∀ r, actualWindowProfile U hU q h A start r = if r ∈ P then (1 : ℝ) else 0) ∧
      (∀ r, actualWindowProfile U hU q h B start r = if r ∈ Q then (1 : ℝ) else 0) ∧
      (P + residues (h : ℕ) B) ∪ (residues (h : ℕ) A + Q) = R := by
  classical
  let f := actualWindowProfile U hU q h A start
  let g := actualWindowProfile U hU q h B start
  have hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1 := fun r =>
    ⟨loebResidueProfile_nonneg U hU q h _ _, loebResidueProfile_le_one U hU q h hd _ _⟩
  have hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1 := fun r =>
    ⟨loebResidueProfile_nonneg U hU q h _ _, loebResidueProfile_le_one U hU q h hd _ _⟩
  have hfzero : ∀ r ∉ residues (h : ℕ) A, f r = 0 :=
    actual_window_profile_zero_outside_residues U hU q h hd A start
  have hgzero : ∀ r ∉ residues (h : ℕ) B, g r = 0 :=
    actual_window_profile_zero_outside_residues U hU q h hd B start
  have hsum (S : Set ℕ) : (∑ r, actualWindowProfile U hU q h S start r) =
      (h : ℕ) * (loebMeasure U hU (internalSet U
        (fun n => (cyclicWindow S (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal :=
    sum_shifted_loebResidueProfile U hU q h _ _
  have hfsum : (∑ r, f r) = (h : ℕ) * a := (hsum A).trans (by rw [hmA])
  have hgsum : (∑ r, g r) = (h : ℕ) * b := (hsum B).trans (by rw [hmB])
  have hRcard : (R.card : ℝ) = (h : ℕ) * (a + b) := by
    calc
      (R.card : ℝ) = ∑ r : ZMod (h : ℕ), if r ∈ R then (1 : ℝ) else 0 := by simp
      _ = ∑ r, actualWindowProfile U hU q h (A + B) start r :=
        Finset.sum_congr rfl (fun r hr => (hR r).symm)
      _ = _ := (hsum (A + B)).trans (by rw [hmC])
  have hnot : ¬residues (h : ℕ) A + residues (h : ℕ) B ⊆ R := by
    intro hsub
    have hbound := gamma_le_of_residue_sum_subset A B R hsub
    have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
    rw [hRcard] at hbound
    have heq : ((h : ℕ) : ℝ) * (a + b) / (h : ℕ) = a + b := by field_simp
    rw [heq] at hbound
    exact not_le_of_gt hgap hbound
  have hleft : ∀ r, ∀ t ∈ residues (h : ℕ) B, f r ≤ if r + t ∈ R then (1 : ℝ) else 0 := by
    intro r t ht
    obtain ⟨n, hn, hnt⟩ := mem_residues.mp ht
    have ht := actual_window_profile_translate_le U hU q hq h hd A B start n hn r
    change f r ≤ actualWindowProfile U hU q h (A + B) start (r + (n : ZMod (h : ℕ))) at ht
    simpa only [hnt, hR] using ht
  have hright : ∀ r ∈ residues (h : ℕ) A, ∀ t, g t ≤ if r + t ∈ R then (1 : ℝ) else 0 := by
    intro r hr t
    obtain ⟨n, hn, hnr⟩ := mem_residues.mp hr
    have ht := actual_window_profile_translate_le U hU q hq h hd B A start n hn t
    change g t ≤ actualWindowProfile U hU q h (B + A) start (t + (n : ZMod (h : ℕ))) at ht
    simpa only [hnr, add_comm B A, add_comm t r, hR] using ht
  have hmass : (∑ r, f r) + (∑ r, g r) = R.card := by
    rw [hfsum, hgsum, hRcard]
    ring
  have hposh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  obtain ⟨hcard, hfFull, hgFull, hfill⟩ := FiniteProfiles.periodic_output_forces_indicator_profiles
    (residues (h : ℕ) A) (residues (h : ℕ) B) R f g hf hg hfzero hgzero
    (by rw [hfsum]; exact mul_pos hposh ha) (by rw [hgsum]; exact mul_pos hposh hb)
    hleft hright hnot hmass
  exact ⟨FiniteProfiles.positiveProfileSupport f, FiniteProfiles.positiveProfileSupport g,
    FiniteProfiles.positiveProfileSupport_subset f _ hfzero,
    FiniteProfiles.positiveProfileSupport_subset g _ hgzero, hcard, hfFull, hgFull, hfill⟩

end Erdos335.Loeb

end
