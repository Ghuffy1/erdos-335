import Erdos335.HighGapProfileConstruction

/-!
# Paired actual-window profiles in the High branch

Private proof development. Verification status is recorded separately. The actual output profiles at the common
physical start are compared explicitly. The two prefix profiles retain
their own zero-start cyclic orders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance highPairedProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_high_gap_paired_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : Bool → ℕ → ℕ+)
    (hdiv : ∀ o, ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q o n : ℕ))
    (hq : ∀ o, Tendsto (fun n => (q o n : ℕ)) atTop atTop)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b δA δB : ℝ)
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
      (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))
    (hDAE : ∀ o, internalSet U (D o) =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))
    (hEsub : ∀ o, ∀ᶠ n in U, E o n ⊆ (if o then A else B))
    (hexhaust : ∀ o, ∀ v ∈ (if o then A else B), ∀ᶠ n in U, v ∈ E o n)
    (hP0 : ∀ o, internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow (if o then A else B) 0 (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))
    (hmMoving : ∀ o, (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal =
        (if o then b else a))
    (hmOther : ∀ o, (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (if o then A else B) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal =
        (if o then a else b))
    (hmC : ∀ o, (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal = a + b)
    (hmE : ∀ o, (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n))).toReal =
        (if o then a else b))
    (hsum : ∀ o, internalSet U (D o) +
      internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
        ≤ᵐ[loebMeasure U hU] internalSet U
          (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))
    (hCagree : ∀ m : ℕ+, ∀ r : ZMod (m : ℕ),
      actualWindowProfile U hU (q false) m (A + B) start r =
        actualWindowProfile U hU (q true) m (A + B) start r) :
    ∃ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 ∧
      ∃ p : LocalPositiveResidueProfile h A B a b
          (fun m r => actualWindowProfile U hU (q false) m A start r)
          (fun m r => actualWindowProfile U hU (q false) m B (fun _ => 0) r)
          (fun m r => actualWindowProfile U hU (q false) m (A + B) start r),
      ∃ r : LocalPositiveResidueProfile h B A b a
          (fun m r => actualWindowProfile U hU (q true) m B start r)
          (fun m r => actualWindowProfile U hU (q true) m A (fun _ => 0) r)
          (fun m r => actualWindowProfile U hU (q false) m (A + B) start r),
        p.movingSupport = residues (h : ℕ) A ∧
        r.movingSupport = residues (h : ℕ) B ∧
        p.movingMass = r.prefixMass ∧ p.prefixMass = r.movingMass ∧
        ∀ m : ℕ+, (h : ℕ) ∣ (m : ℕ) →
          (∀ t : ZMod (m : ℕ), actualWindowProfile U hU (q false) m A start t =
            actualWindowProfile U hU (q true) m A (fun _ => 0) t) ∧
          (∀ t : ZMod (m : ℕ), actualWindowProfile U hU (q true) m B start t =
            actualWindowProfile U hU (q false) m B (fun _ => 0) t) := by
  classical
  have hgammaSwap : gamma B A = gamma A B := by
    unfold gamma modularCapacity
    simp only [add_comm]
  obtain ⟨h, hbound, ⟨p⟩⟩ := exists_local_positive_profile_of_high_gaps U hU (q false)
    (hdiv false) (hq false) A B start a b δA δB ha hb hAdensity hBdensity hCdensity
    hgap hhighA hhighB hcapA hcapB (D false) (E false) (hDsub false) (hDAE false)
    (hEsub false) (hexhaust false) (hP0 false) (hmMoving false) (hmOther false) (hmC false)
    (hmE false) (hsum false)
  obtain ⟨k, _, ⟨r⟩⟩ := exists_local_positive_profile_of_high_gaps U hU (q true)
    (hdiv true) (hq true) B A start b a δB δA hb ha hBdensity hAdensity
    (by simpa only [add_comm A B, add_comm a b] using hCdensity)
    (by simpa only [hgammaSwap, add_comm b a] using hgap)
    (by simpa only [hgammaSwap, add_comm b a] using hhighB)
    (by simpa only [hgammaSwap, add_comm b a] using hhighA)
    hcapB hcapA (D true) (E true) (hDsub true) (hDAE true) (hEsub true) (hexhaust true)
    (hP0 true) (hmMoving true) (hmOther true)
    (by simpa only [add_comm A B, add_comm a b] using hmC true) (hmE true)
    (by simpa only [add_comm A B] using hsum true)
  let r' : LocalPositiveResidueProfile k B A b a
      (fun m t => actualWindowProfile U hU (q true) m B start t)
      (fun m t => actualWindowProfile U hU (q true) m A (fun _ => 0) t)
      (fun m t => actualWindowProfile U hU (q false) m (A + B) start t) :=
    { r with
      output_profile := by
        intro m hm t
        exact (hCagree m t).trans (by simpa only [add_comm A B] using r.output_profile m hm t)
    }
  obtain ⟨hhk, hSA, hSB, hx, hy, hprofiles⟩ := paired_positive_profiles_match h k A B a b
    (fun m t => actualWindowProfile U hU (q false) m A start t)
    (fun m t => actualWindowProfile U hU (q true) m B start t)
    (fun m t => actualWindowProfile U hU (q true) m A (fun _ => 0) t)
    (fun m t => actualWindowProfile U hU (q false) m B (fun _ => 0) t)
    (fun m t => actualWindowProfile U hU (q false) m (A + B) start t) p r'
  subst k
  exact ⟨h, hbound, p, r', hSA, hSB, hx, hy, hprofiles⟩

end Erdos335.Loeb

end
