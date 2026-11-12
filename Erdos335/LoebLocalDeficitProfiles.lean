import Erdos335.LoebPeriodicWindowProfiles
import Erdos335.LocalTemplate

/-!
# Local deficit compensation for actual cyclic-window profiles
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped BigOperators ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance localDeficitProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_window_local_deficit_template
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun s => (q s : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B) (S : Finset (ZMod (h : ℕ)))
    (hSR : S ⊆ residues (h : ℕ) A)
    (hcard : (S + residues (h : ℕ) B).card + 1 = S.card + (residues (h : ℕ) B).card)
    (hzero : ∀ r ∉ S, actualWindowProfile U hU q h A start r = 0)
    (hcore : ∀ r ∈ S + residues (h : ℕ) B, actualWindowProfile U hU q h (A + B) start r = 1)
    (hdeficit : ((S + residues (h : ℕ) B).card : ℝ) < ((h : ℕ) : ℝ) * (a + b)) :
    let R := residues (h : ℕ) A
    let T := residues (h : ℕ) B
    ∃ r t : ZMod (h : ℕ), r ∈ R ∧ t ∈ T ∧ r ∉ S ∧ R = insert r S ∧
      (R + T) \ (S + T) = {r + t} ∧
      (∀ s ∈ S, actualWindowProfile U hU q h A start s = 1) ∧
      (∀ y ∈ T.erase t, actualWindowProfile U hU q h B start y = 1) ∧
      actualWindowProfile U hU q h B start t = ((h : ℕ) : ℝ) * b - ((T.card : ℝ) - 1) ∧
      ((h : ℕ) : ℝ) * b - ((T.card : ℝ) - 1) < 1 ∧
      ∀ x ∈ R, ∀ y ∈ T, x + y = r + t → x = r ∧ y = t := by
  classical
  dsimp only
  let R := residues (h : ℕ) A
  let T := residues (h : ℕ) B
  let f := actualWindowProfile U hU q h A start
  let g := actualWindowProfile U hU q h B start
  let c := actualWindowProfile U hU q h (A + B) start
  have sum_of_support (p : ZMod (h : ℕ) → ℝ) (V : Finset (ZMod (h : ℕ)))
      (hz : ∀ r ∉ V, p r = 0) : (∑ r ∈ V, p r) = ∑ r, p r := by
    apply Finset.sum_subset (Finset.subset_univ V)
    exact fun r hr hn => hz r hn
  have hsum (E : Set ℕ) : (∑ r, actualWindowProfile U hU q h E start r) =
      (h : ℕ) * (loebMeasure U hU (internalSet U
        (fun n => (cyclicWindow E (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal :=
    sum_shifted_loebResidueProfile U hU q h _ _
  have hf : (∑ r ∈ S, f r) = ((h : ℕ) : ℝ) * a := by
    rw [sum_of_support f S hzero]
    exact (hsum A).trans (by rw [hmA])
  have hgzero : ∀ r ∉ T, g r = 0 := actual_window_profile_zero_outside_residues U hU q h hd B start
  have hg : (∑ r ∈ T, g r) = ((h : ℕ) : ℝ) * b := by
    rw [sum_of_support g T hgzero]
    exact (hsum B).trans (by rw [hmB])
  have hczero : ∀ r ∉ R + T, c r = 0 := by
    intro r hr
    apply actual_window_profile_zero_outside_residues U hU q h hd (A + B) start r
    simpa only [R, T, residues_add] using hr
  have hc : (∑ r ∈ R + T, c r) = ((h : ℕ) : ℝ) * (a + b) := by
    rw [sum_of_support c (R + T) hczero]
    exact (hsum (A + B)).trans (by rw [hmC])
  have hmass : (∑ r ∈ R + T, c r) = (∑ r ∈ S, f r) + ∑ r ∈ T, g r := by
    rw [hf, hg, hc]
    ring
  have hf1 (r : ZMod (h : ℕ)) : f r ≤ 1 := loebResidueProfile_le_one U hU q h hd _ _
  have hg1 (r : ZMod (h : ℕ)) : g r ≤ 1 := loebResidueProfile_le_one U hU q h hd _ _
  have hhpos : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hextra : ¬R + T ⊆ S + T := by
    intro hsub
    have hbound := gamma_le_of_residue_sum_subset A B (S + T) hsub
    have hcoreSmall : ((S + T).card : ℝ) / (h : ℕ) < a + b := (div_lt_iff₀ hhpos).mpr (by
      simpa only [mul_comm] using hdeficit)
    exact not_lt_of_ge hbound (hcoreSmall.trans hgap)
  have hfg : (∑ r ∈ S, f r) ≤ (S.card : ℝ) := by
    simpa using Finset.sum_le_sum (fun r hr => hf1 r)
  have hcardR : ((S + T).card : ℝ) + 1 = (S.card : ℝ) + T.card := by exact_mod_cast hcard
  have he : 0 < (∑ r ∈ T, g r) - ((T.card : ℝ) - 1) := by
    rw [hg]
    rw [hf] at hfg
    change ((S + T).card : ℝ) < ((h : ℕ) : ℝ) * (a + b) at hdeficit
    nlinarith
  have hcGap : (∑ r ∈ R + T, c r) < ((R + T).card : ℝ) := by
    rw [hc]
    have hbound := gamma_le_modularCapacity A B h
    change gamma A B ≤ ((R + T).card : ℝ) / (h : ℕ) at hbound
    have hstrict := hgap.trans_le hbound
    have hmul := (lt_div_iff₀ hhpos).mp hstrict
    simpa only [mul_comm] using hmul
  have htranslate : ∀ r ∈ R, ∀ t ∈ T, g t ≤ c (r + t) := by
    intro r hr t ht
    obtain ⟨n, hn, hnr⟩ := mem_residues.mp hr
    have hb := actual_window_profile_translate_le U hU q hq h hd B A start n hn t
    change g t ≤ actualWindowProfile U hU q h (B + A) start (t + (n : ZMod (h : ℕ))) at hb
    simpa only [hnr, add_comm B A, add_comm t r] using hb
  obtain ⟨r, t, hr, ht, hrs, hR, hdiff, hffull, hgfull, hgt, hgt1, hunique⟩ :=
    FiniteProfiles.local_deficit_template R S T f g c hSR hcard hextra
      (fun r hr => hf1 r) (fun t ht => hg1 t)
      (fun r hr => loebResidueProfile_nonneg U hU q h _ _) hcore htranslate hmass he hcGap
  rw [hg] at hgt hgt1
  exact ⟨r, t, hr, ht, hrs, hR, hdiff, hffull, hgfull, hgt, hgt1, hunique⟩

end Erdos335.Loeb

end
