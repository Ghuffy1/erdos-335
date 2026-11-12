import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Endpoint differences capturing the measure of a bounded real set
-/

set_option autoImplicit false

open Set MeasureTheory

namespace Erdos335.Loeb

theorem exists_endpoints_cover_measure
    (B : Set ℝ) (hbelow : BddBelow B) (habove : BddAbove B)
    (hpositive : 0 < volume B) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ B, ∃ y ∈ B, x < y ∧ (volume B).toReal ≤ (1 + ε) * (y - x) := by
  have hB : B.Nonempty := nonempty_of_measure_ne_zero hpositive.ne'
  let a := sInf B
  let b := sSup B
  have hab : a ≤ b := csInf_le_csSup hB hbelow habove
  have hsub : B ⊆ Icc a b := fun x hx => ⟨csInf_le hbelow hx, le_csSup habove hx⟩
  have hvolume : volume B ≤ ENNReal.ofReal (b - a) := by
    simpa only [Real.volume_Icc] using (measure_mono (μ := volume) hsub)
  have hfinite : volume B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolume
  have hrealpos : 0 < (volume B).toReal := ENNReal.toReal_pos hpositive.ne' hfinite
  have hreal : (volume B).toReal ≤ b - a := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvolume
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h
  let d : ℝ := (volume B).toReal / (1 + ε)
  have hden : 0 < 1 + ε := by linarith
  have hd : d < b - a := by
    have hstrict : d < (volume B).toReal := by
      dsimp [d]
      apply (div_lt_iff₀ hden).mpr
      nlinarith
    exact hstrict.trans_le hreal
  have hgap : 0 < (b - a - d) / 3 := by linarith
  obtain ⟨x, hx, hxa⟩ := exists_lt_of_csInf_lt hB (show a < a + (b - a - d) / 3 by linarith)
  obtain ⟨y, hy, hyb⟩ := exists_lt_of_lt_csSup hB (show b - (b - a - d) / 3 < b by linarith)
  have hdiff : d < y - x := by linarith
  have hdpos : 0 < d := div_pos hrealpos hden
  refine ⟨x, hx, y, hy, by linarith, ?_⟩
  have hmul := (div_lt_iff₀ hden).mp hdiff
  nlinarith

end Erdos335.Loeb
