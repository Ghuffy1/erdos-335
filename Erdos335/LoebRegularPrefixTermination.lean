import Erdos335.LoebRegularQuasiPeriodBound
import Erdos335.LoebGeneralInverseIteration

/-!
# Termination from a regular prefix and a strict literal output gap
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance regularPrefixTerminationLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_regular_prefix_aperiodic_inverse
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
    (hWpos : 0 < loebMeasure U hU (internalSet U D))
    (hPpos : 0 < loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hfull : loebMeasure U hU
      (internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) =
        loebMeasure U hU (internalSet U D) +
          loebMeasure U hU (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hmodelC : internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hgap : a + b < gamma A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ
        (internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))
          =ᵐ[loebMeasure U hU]
            internalSet U D + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) :
    let W := internalSet U D
    let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
    Nonempty (InternalBohrPairData U hU q W P) ∨
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) W P,
        loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0 ∨
          Nonempty (InternalBohrPairData U hU q p.left.active p.right.active) := by
  dsimp only
  let W := internalSet U D
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  have hSm : MeasurableSet (W + P) := by
    dsimp only [W, P]
    rw [← internalSet_add]
    exact measurable_internalSet U _
  rcases loeb_aperiodic_inverse_iteration_alternative U hU q W P
      (measurable_internalSet U _) (measurable_internalSet U _) hSm hWpos hPpos hfull hnoAE with
    hbohr | hterminal | hsmall
  · exact Or.inl hbohr
  · exact Or.inr hterminal
  · obtain ⟨p, hp⟩ := hsmall (gamma A B - (a + b)) (sub_pos.mpr hgap)
    by_cases hzero : loebMeasure U hU p.right.active = 0
    · exact Or.inr ⟨p, Or.inr (Or.inl hzero)⟩
    have hpositive := pos_iff_ne_zero.mpr hzero
    obtain ⟨h, ρ, hρ, hkerρ, hmass⟩ := positive_measurable_subgroup_is_natural_finite_kernel U hU q
      p.period p.period_measurable p.period_positive
    have hρeq := finiteQuotient_eq_of_eventually_natural U q h ρ
      (fun n => naturalCyclicProjection (q n) h) (hρ.mono fun n hn => hn.2)
      ((hdiv h).mono fun n hn v => naturalCyclicProjection_natCast (q n) h hn v)
    have hker : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker = p.period := by
      rw [← hρeq]
      exact hkerρ
    have hbound := loeb_regular_prefix_quasi_period_bound U hU q hdiv hq A B start a b D E
      hDsub hDAE hEsub hexhaust hmA hmB hmE happroxB p hpositive hfull hmodelC
      (hnoAE p.period p.period_measurable p.period_positive) h hker
    rw [hmass, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast] at hp
    exact False.elim (by linarith)

end Erdos335.Loeb

end
