import Erdos335.LoebActualWindowInverse
import Erdos335.LoebRegularBohrExclusion
import Erdos335.LoebLiteralActiveSize
import Erdos335.LoebLiteralFiberPoints
import Erdos335.LoebLiteralDifferencePeriods
import Erdos335.LoebRegularWindowPeriod

/-!
# A regular input window paired with a positive-gap literal prefix
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance regularActualWindowInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_regular_actual_window_is_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
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
    (hgap : a + b < gamma A B)
    (hcapacity : ∀ h : ℕ+, b + δ ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε) :
    ∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))), (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU] (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) := by
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let W := internalSet U D
  have hexclude := loeb_regular_window_no_positive_terminal U hU q hdiv P W A start hDAE a hmA happrox
  rcases loeb_actual_window_inverse U hU q hq A B start a b δ ha hb hδ D E hDsub hDAE hEsub
    hexhaust hmA hmB hmC hmE hsum hgap hcapacity with hmask | hbohr | ⟨p, hterminal⟩
  · exact hmask
  · exact False.elim (hexclude.1 hbohr)
  · rcases hterminal with hzero | hbohr
    · have hactive := loeb_literal_active_not_subsingleton U hU q hdiv B E hEsub hexhaust b δ hδ
        hmE hcapacity p.period p.period_measurable p.period_positive p.left
      obtain ⟨m, ρ, hρ, hker, _⟩ := positive_measurable_subgroup_is_natural_finite_kernel U hU q
        p.period p.period_measurable p.period_positive
      have hnat := hρ.mono fun n hn => hn.2
      obtain ⟨x, y, hx, hy, hxy, hxr, hyr⟩ := literal_active_has_two_integers U hU q B E hEsub
        p.period p.left hactive m ρ hnat hker
      have hSm : MeasurableSet (W + P) := by
        dsimp only [W, P]
        rw [← internalSet_add]
        exact measurable_internalSet U _
      have hperiod := (loeb_literal_null_active_difference_periods U hU q B E D hexhaust p.swap
        hSm hzero m ρ hnat hker y x hxy hy hx hyr hxr).1
      let t : ℕ+ := ⟨y - x, Nat.sub_pos_of_lt hxy⟩
      have hactual : productProjection (U : Filter ℕ) (fun n => ((t : ℕ) : ZMod (q n : ℕ))) +ᵥ
          internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
          =ᵐ[loebMeasure U hU]
            internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) :=
        (loeb_vadd_congr_ae U hU _ _
          (productProjection (U : Filter ℕ) (fun n => ((t : ℕ) : ZMod (q n : ℕ)))) hDAE.symm).trans
            (hperiod.trans hDAE)
      obtain ⟨R, hR⟩ := loeb_regular_window_period_is_mask U hU q hdiv A start a hmA happrox t hactual
      exact ⟨t, R, hdiv t, hR⟩
    · exact False.elim (hexclude.2 p hbohr)

end Erdos335.Loeb

end
