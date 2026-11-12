import Erdos335.LoebRefinementBound
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Iteration of active-pair refinements

If every quasi-periodic decomposition of the fixed pair admits another
quasi-periodic active pair, there are decompositions with arbitrarily small
period measure. The refinement bound supplies geometric decay.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicIterationLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_arbitrarily_small_of_refinable
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hrefine : ∀ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
        r.left.active r.right.active))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      (loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (r.period : Set _)).toReal < ε := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let P := QuasiPeriodicPairData μ (internalInnerMeasure U hU) A B
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let step (r : P) : P :=
    (loeb_quasiPeriodic_refinement U hU q A B r (Classical.choice (hrefine r))).choose
  have hstep (r : P) : μ ((step r).period : Set G) + μ ((step r).period : Set G) ≤ μ (r.period : Set G) :=
    (loeb_quasiPeriodic_refinement U hU q A B r (Classical.choice (hrefine r))).choose_spec.2.2.2
  let sequence : ℕ → P := Nat.rec p (fun _ r => step r)
  let mass : ℕ → ℝ := fun n => (μ ((sequence n).period : Set G)).toReal
  have hdec (n : ℕ) : mass (n + 1) ≤ (1 / 2 : ℝ) * mass n := by
    have h := ENNReal.toReal_mono (measure_ne_top μ _) (hstep (sequence n))
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h
    change mass (n + 1) + mass (n + 1) ≤ mass n at h
    linarith
  have hbound (n : ℕ) : mass n ≤ (1 / 2 : ℝ) ^ n * mass 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        mass (n + 1) ≤ (1 / 2 : ℝ) * mass n := hdec n
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * mass 0) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) * mass 0 := by rw [pow_succ]; ring
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto mass atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound
    simpa only [zero_mul] using hpow.mul_const (mass 0)
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hε)).exists
  exact ⟨sequence n, hn⟩

end Erdos335.Loeb

end
