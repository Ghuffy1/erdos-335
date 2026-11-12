import Erdos335.LoebLiteralGapTermination
import Erdos335.NaturalCyclicProjection

/-!
# A quantitative natural-index bound for literal-prefix periods
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance literalPeriodIndexLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_literal_quasi_period_index_le
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ℕ) (E : ℕ → Set ℕ)
    (hEA : ∀ᶠ n in U, E n ⊆ A) (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (a δ : ℝ) (hδ : 0 < δ)
    (hmass : (loebMeasure U hU (internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = a)
    (hcapacity : ∀ h : ℕ+, a + δ ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hker : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker = H) :
    ((h : ℕ) : ℝ) ≤ 1 / δ := by
  have hgap := loeb_literal_exhaustion_saturation_gap U hU q A E hEA hexhaust a δ hmass hcapacity H hHm hHpos
  have hbound := loeb_quasiPeriodic_period_bound_of_saturation_gap U hU q _ H p δ hgap
  rw [← hker, finiteQuotient_ker, loebMeasure_internalSubgroup_of_eventually_quotients U hU
    (fun n => naturalCyclicProjection (q n) h)
    (hd.mono fun n hn => naturalCyclicProjection_surjective (q n) h hn),
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast] at hbound
  rw [Nat.card_zmod] at hbound
  have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hproduct : δ * (h : ℕ) ≤ 1 := (le_div_iff₀ hh).mp hbound
  apply (le_div_iff₀ hδ).mpr
  simpa only [mul_comm] using hproduct

end Erdos335.Loeb

end
