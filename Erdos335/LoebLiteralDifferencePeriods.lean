import Erdos335.LoebNullActivePeriods
import Erdos335.LoebLiteralResidues

/-!
# Literal integer differences in a null active residue class
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance literalDifferencePeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_literal_null_active_difference_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (B : Set ℕ) (E : ℕ → Set ℕ) (W : ∀ n, Set (ZMod (q n : ℕ)))
    (hexhaust : ∀ b ∈ B, ∀ᶠ n in U, b ∈ E n)
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (internalSet U W) (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hSm : MeasurableSet (internalSet U W +
      internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hzero : loebMeasure U hU p.right.active = 0)
    (h : ℕ+) (ρ : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ))
    (hρ : ∀ᶠ n in U, ∀ b : ℕ, ρ n (b : ZMod (q n : ℕ)) = (b : ZMod (h : ℕ)))
    (hker : (finiteQuotient U ρ).ker = p.period)
    (x y : ℕ) (hyx : y < x) (hx : x ∈ B) (hy : y ∈ B)
    (hxr : (x : ZMod (h : ℕ)) = finiteQuotient U ρ p.right.anchor)
    (hyr : (y : ZMod (h : ℕ)) = finiteQuotient U ρ p.right.anchor) :
    let t := productProjection (U : Filter ℕ) (fun n => ((x - y : ℕ) : ZMod (q n : ℕ)))
    t +ᵥ internalSet U W =ᵐ[loebMeasure U hU] internalSet U W ∧
      t +ᵥ (internalSet U W + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))
        =ᵐ[loebMeasure U hU]
          internalSet U W + internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) := by
  dsimp only
  let point := fun b : ℕ => productProjection (U : Filter ℕ) (fun n => (b : ZMod (q n : ℕ)))
  have active_mem (b : ℕ) (hb : b ∈ B)
      (hr : (b : ZMod (h : ℕ)) = finiteQuotient U ρ p.right.anchor) : point b ∈ p.right.active := by
    rw [p.right.active_eq_inter_coset]
    refine ⟨?_, ?_⟩
    · change ∀ᶠ n in U, (b : ZMod (q n : ℕ)) ∈ ((↑) : ℕ → ZMod (q n : ℕ)) '' E n
      exact (hexhaust b hb).mono fun n hn => ⟨b, hn, rfl⟩
    · have heq : finiteQuotient U ρ (point b) = finiteQuotient U ρ p.right.anchor :=
        (finiteQuotient_natCast_of_eventually U q h ρ hρ b).trans hr
      have hk : point b - p.right.anchor ∈ (finiteQuotient U ρ).ker := by
        change finiteQuotient U ρ (point b - p.right.anchor) = 0
        rw [map_sub, heq, sub_self]
      have hp : point b - p.right.anchor ∈ p.period := hker.le hk
      exact ⟨point b - p.right.anchor, hp, by simp only [vadd_eq_add, add_sub_cancel]⟩
  have hperiod := loeb_null_right_active_difference_periods U hU q _ _ p hSm hzero
    (point x) (point y) (active_mem x hx hxr) (active_mem y hy hyr)
  have hpoints : point x - point y =
      productProjection (U : Filter ℕ) (fun n => ((x - y : ℕ) : ZMod (q n : ℕ))) := by
    change productProjection (U : Filter ℕ) (fun n => (x : ZMod (q n : ℕ)) - (y : ZMod (q n : ℕ))) = _
    congr 1
    funext n
    exact (Nat.cast_sub hyx.le).symm
  rwa [hpoints] at hperiod

end Erdos335.Loeb

end
