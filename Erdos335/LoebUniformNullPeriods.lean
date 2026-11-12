import Erdos335.FiniteDifferenceRepresentatives
import Erdos335.LoebLiteralPeriodIndex
import Erdos335.LoebLiteralActiveSize
import Erdos335.LoebLiteralFiberPoints
import Erdos335.LoebLiteralDifferencePeriods

/-!
# A fixed finite family of integer periods for null literal-prefix terminals
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance uniformNullPeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_uniform_literal_null_periods
    (B : Set ℕ) (b δ : ℝ) (hδ : 0 < δ)
    (hcapacity : ∀ h : ℕ+, b + δ ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) :
    ∃ F : Finset ℕ, (∀ t ∈ F, 0 < t) ∧
      ∀ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+),
        (∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) →
        ∀ (E : ℕ → Set ℕ) (W : ∀ n, Set (ZMod (q n : ℕ))),
          (∀ᶠ n in U, E n ⊆ B) → (∀ v ∈ B, ∀ᶠ n in U, v ∈ E n) →
          (loebMeasure U hU (internalSet U
            (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = b →
          ∀ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
            (internalSet U W) (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)),
            loebMeasure U hU p.right.active = 0 →
            ∃ t ∈ F,
              productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ))) +ᵥ internalSet U W
                =ᵐ[loebMeasure U hU] internalSet U W ∧
              productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ))) +ᵥ
                (internalSet U W + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))
                  =ᵐ[loebMeasure U hU]
                    internalSet U W + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) := by
  classical
  let N := Nat.ceil (1 / δ)
  obtain ⟨F, hF, hselect⟩ := finite_residue_difference_representatives B N
  refine ⟨F, hF, ?_⟩
  intro U hU q hdiv E W hEsub hexhaust hmass p hzero
  obtain ⟨h, ρ, hρ, hkerρ, _⟩ := positive_measurable_subgroup_is_natural_finite_kernel U hU q
    p.period p.period_measurable p.period_positive
  have hnatural := hρ.mono fun n hn => hn.2
  have hρeq := finiteQuotient_eq_of_eventually_natural U q h ρ
    (fun n => naturalCyclicProjection (q n) h) hnatural
    ((hdiv h).mono fun n hn v => naturalCyclicProjection_natCast (q n) h hn v)
  have hker : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker = p.period := by
    rw [← hρeq]
    exact hkerρ
  have hindex := loeb_literal_quasi_period_index_le U hU q B E hEsub hexhaust b δ hδ hmass hcapacity
    p.period p.period_measurable p.period_positive p.right h (hdiv h) hker
  have hleN : (h : ℕ) ≤ N := by
    exact_mod_cast hindex.trans (Nat.le_ceil (1 / δ))
  have hactive := loeb_literal_active_not_subsingleton U hU q hdiv B E hEsub hexhaust b δ hδ
    hmass hcapacity p.period p.period_measurable p.period_positive p.right
  obtain ⟨x, y, hx, hy, hxy, hxr, hyr⟩ := literal_active_has_two_integers U hU q B E hEsub
    p.period p.right hactive h ρ hnatural hkerρ
  obtain ⟨u, hu, v, hv, huv, hur, hvr, hdiff⟩ := hselect h (finiteQuotient U ρ p.right.anchor) hleN
    ⟨x, hx, y, hy, hxy, hxr, hyr⟩
  have hSm : MeasurableSet (internalSet U W + internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) := by
    rw [← internalSet_add]
    exact measurable_internalSet U _
  exact ⟨v - u, hdiff, loeb_literal_null_active_difference_periods U hU q B E W hexhaust p hSm
    hzero h ρ hnatural hkerρ v u huv hv hu hvr hur⟩

end Erdos335.Loeb

end
