import Erdos335.HighGapPairedProfiles
import Erdos335.ConstrainedProfileComparison
import Erdos335.ConstrainedPhysicalProfileLimits

/-!
# High-branch profiles at the original reference scale

Private proof development. Verification status is recorded separately. This invokes the actual paired High theorem
on the supplied Loeb models. Both selected cyclic lengths approximate the
same fixed reference length H and use the same physical start.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance highFixedScaleLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem high_gap_fixed_scale_window_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : Bool → ℕ → ℕ+)
    (hdiv : ∀ o, ∀ h : ℕ+, ∀ᶠ n in atTop, (h : ℕ) ∣ (q o n : ℕ))
    (hq : ∀ o, Tendsto (fun n => (q o n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start H : ℕ → ℕ) (a b δA δB : ℝ)
    (hH : ∀ n, 0 < H n) (hHq : ∀ o n, H n ≤ (q o n : ℕ))
    (hqgap : ∀ o, Tendsto (fun n => (((q o n : ℕ) - H n : ℕ) : ℝ) /
      (q o n : ℕ)) atTop (𝓝 0))
    (ha : 0 < a) (hb : 0 < b)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b))
    (hgap : a + b < gamma A B)
    (hhighA : gamma A B < a + b + δA)
    (hhighB : gamma A B < a + b + δB)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (D : ∀ o n, Set (ZMod (q o n : ℕ))) (E : Bool → ℕ → Set ℕ)
    (hDsub : ∀ o, internalSet U (D o) ⊆ internalSet U
      (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) :
        Set (ZMod (q o n : ℕ)))))
    (hDAE : ∀ o, internalSet U (D o) =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) :
        Set (ZMod (q o n : ℕ)))))
    (hEsub : ∀ o, ∀ᶠ n in U, E o n ⊆ (if o then A else B))
    (hexhaust : ∀ o, ∀ v ∈ (if o then A else B), ∀ᶠ n in U, v ∈ E o n)
    (hP0 : ∀ o, internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (if o then A else B) 0 (q o n : ℕ) :
          Set (ZMod (q o n : ℕ)))))
    (hmMoving : ∀ o, (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) :
        Set (ZMod (q o n : ℕ)))))).toReal = (if o then b else a))
    (hmOther : ∀ o, (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (if o then A else B) (start n) (q o n : ℕ) :
        Set (ZMod (q o n : ℕ)))))).toReal = (if o then a else b))
    (hmC : ∀ o, (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) :
        Set (ZMod (q o n : ℕ)))))).toReal = a + b)
    (hmE : ∀ o, (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n))).toReal =
        (if o then a else b))
    (hsum : ∀ o, internalSet U (D o) +
      internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
        ≤ᵐ[loebMeasure U hU] internalSet U
          (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) :
            Set (ZMod (q o n : ℕ)))))
    (M : ℕ+)
    (hM : ∀ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 →
      (h : ℕ) ∣ (M : ℕ))
    (vA vB : ZMod (M : ℕ) → ℝ)
    (hprefixA : ∀ r, Tendsto (fun n => ((M : ℕ) : ℝ) *
      ((prefixCount {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r} (H n) : ℝ) / H n))
        atTop (𝓝 (vA r)))
    (hprefixB : ∀ r, Tendsto (fun n => ((M : ℕ) : ℝ) *
      ((prefixCount {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r} (H n) : ℝ) / H n))
        atTop (𝓝 (vB r))) :
    (∀ r, Tendsto (fun n => ((M : ℕ) : ℝ) *
      (((@cyclicWindow {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r}
        (start n) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)) (U : Filter ℕ) (𝓝 (vA r))) ∧
    (∀ r, Tendsto (fun n => ((M : ℕ) : ℝ) *
      (((@cyclicWindow {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r}
        (start n) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)) (U : Filter ℕ) (𝓝 (vB r))) := by
  have hdivU : ∀ o, ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q o n : ℕ) :=
    fun o h => (hdiv o h).filter_mono hU
  have hCagree (m : ℕ+) (r : ZMod (m : ℕ)) :
      actualWindowProfile U hU (q false) m (A + B) start r =
        actualWindowProfile U hU (q true) m (A + B) start r :=
    constrained_actual_window_profiles_agree U hU (A + B) start H (q false) (q true)
      hH (hHq false) (hHq true) (hqgap false) (hqgap true) m
        (hdiv false m) (hdiv true m) r
  obtain ⟨h, hbound, p, p', _, _, _, _, hprofiles⟩ := exists_high_gap_paired_profiles
    U hU q hdivU hq A B start a b δA δB ha hb hAdensity hBdensity hCdensity
      hgap hhighA hhighB hcapA hcapB D E hDsub hDAE hEsub hexhaust hP0
        hmMoving hmOther hmC hmE hsum hCagree
  have hmatch := hprofiles M (hM h hbound)
  constructor
  · intro r
    have hpref : actualWindowProfile U hU (q true) M A (fun _ => 0) r = vA r :=
      constrained_prefix_profile_eq_limit U hU H (q true) hH (hHq true) (hqgap true)
        A M (hdiv true M) r (vA r) (hprefixA r)
    exact reference_window_profile_tendsto_of_actual_profile U hU H (q false)
      hH (hHq false) (hqgap false) A start M (hdivU false M) r (vA r)
        ((hmatch.1 r).trans hpref)
  · intro r
    have hpref : actualWindowProfile U hU (q false) M B (fun _ => 0) r = vB r :=
      constrained_prefix_profile_eq_limit U hU H (q false) hH (hHq false) (hqgap false)
        B M (hdiv false M) r (vB r) (hprefixB r)
    exact reference_window_profile_tendsto_of_actual_profile U hU H (q true)
      hH (hHq true) (hqgap true) B start M (hdivU true M) r (vB r)
        ((hmatch.2 r).trans hpref)

theorem not_eventually_separated_of_tendsto
    (U : Ultrafilter ℕ) (f : ℕ → ℝ) (v ε : ℝ) (hε : 0 < ε)
    (hlimit : Tendsto f (U : Filter ℕ) (𝓝 v))
    (hbad : ∀ᶠ n in U, ε ≤ |f n - v|) : False := by
  have habs : Tendsto (fun n => |f n - v|) (U : Filter ℕ) (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (hlimit.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) (U : Filter ℕ) (𝓝 v))).abs
  obtain ⟨n, hn, hsmall⟩ := (hbad.and (habs.eventually (gt_mem_nhds hε))).exists
  exact (not_lt_of_ge hn) hsmall

end Erdos335.Loeb

end
