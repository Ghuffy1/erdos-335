import Erdos335.LoebLiteralGapTermination
import Erdos335.BlockCounting

/-!
# Cyclic models of ordinary integer prefixes

The half-open prefix embeds injectively into the cyclic group of the same
size. Its Loeb measure is the ordinary density, and its finite quotient
images retain every literal residue of the original integer set.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

def cyclicIntegerPrefix (A : Set ℕ) (q : ℕ+) : Set (ZMod (q : ℕ)) :=
  ((↑) : ℕ → ZMod (q : ℕ)) '' (A ∩ Iio (q : ℕ))

theorem cyclicIntegerPrefix_ncard (A : Set ℕ) (q : ℕ+) :
    (cyclicIntegerPrefix A q).ncard = prefixCount A q := by
  classical
  have hinj : Set.InjOn ((↑) : ℕ → ZMod (q : ℕ)) (A ∩ Iio (q : ℕ)) := by
    intro a ha b hb hab
    have hv := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha.2, ZMod.val_natCast_of_lt hb.2] at hv
  have hset : A ∩ Iio (q : ℕ) = (((Finset.range (q : ℕ)).filter (· ∈ A)) : Set ℕ) := by
    ext a
    simp only [mem_inter_iff, mem_Iio, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact and_comm
  rw [cyclicIntegerPrefix, hinj.ncard_image, hset, Set.ncard_coe_finset]
  rfl

local instance integerPrefixesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loebMeasure_cyclicIntegerPrefix
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A : Set ℕ) (α : ℝ) (hA : HasDensity A α) :
    (loebMeasure U hU (internalSet U (fun n => cyclicIntegerPrefix A (q n)))).toReal = α := by
  rw [loebMeasure_internal]
  have hfinite : ultraCount U (fun n => cyclicIntegerPrefix A (q n)) ≠ ∞ :=
    ne_of_lt ((ultraCount_le_one U _).trans_lt ENNReal.one_lt_top)
  have hfirst := (ENNReal.tendsto_toReal hfinite).comp
    (tendsto_ultraCount U (fun n => cyclicIntegerPrefix A (q n)))
  have hsecond := (((hasDensity_iff_prefixCount A α).mp hA).comp hq).mono_left hU
  have hcount (n : ℕ) : (countingRatio (cyclicIntegerPrefix A (q n))).toReal =
      (prefixCount A (q n) : ℝ) / (q n : ℕ) := by
    rw [countingRatio_toReal, cyclicIntegerPrefix_ncard]
    simp
  apply tendsto_nhds_unique hfirst
  exact hsecond.congr (fun n => (hcount n).symm)

theorem cyclicIntegerPrefix_exhaustion
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop) (A : Set ℕ) :
    ∀ a ∈ A, ∀ᶠ n in U, a ∈ A ∩ Iio (q n : ℕ) := by
  intro a ha
  apply ((hq.mono_left hU).eventually (eventually_gt_atTop a)).mono
  intro n hn
  exact ⟨ha, hn⟩

theorem loeb_cyclicIntegerPrefix_inverse
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A : Set ℕ) (α δ : ℝ) (hA : HasDensity A α) (hα : 0 < α) (hδ : 0 < δ)
    (hcapacity : ∀ h : ℕ+, α + δ ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hBm : MeasurableSet B) (hBpos : 0 < loebMeasure U hU B)
    (hSm : MeasurableSet (internalSet U (fun n => cyclicIntegerPrefix A (q n)) + B))
    (hfull : loebMeasure U hU (internalSet U (fun n => cyclicIntegerPrefix A (q n)) + B) =
      loebMeasure U hU (internalSet U (fun n => cyclicIntegerPrefix A (q n))) + loebMeasure U hU B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (internalSet U (fun n => cyclicIntegerPrefix A (q n)) + B)
        =ᵐ[loebMeasure U hU] internalSet U (fun n => cyclicIntegerPrefix A (q n)) + B) :
    Nonempty (InternalBohrPairData U hU q (internalSet U (fun n => cyclicIntegerPrefix A (q n))) B) ∨
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
        (internalSet U (fun n => cyclicIntegerPrefix A (q n))) B,
        loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0 ∨
          Nonempty (InternalBohrPairData U hU q p.left.active p.right.active) := by
  exact loeb_literal_exhaustion_inverse U hU q A (fun n => A ∩ Iio (q n : ℕ))
    (Eventually.of_forall fun _ => inter_subset_left) (cyclicIntegerPrefix_exhaustion U hU q hq A)
    B α δ hα hδ (loebMeasure_cyclicIntegerPrefix U hU q hq A α hA)
    hcapacity hBm hBpos hSm hfull hnoAE

end Erdos335.Loeb

end
