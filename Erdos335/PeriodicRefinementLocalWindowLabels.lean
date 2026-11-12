import Erdos335.DenseCyclicRemoval
import Erdos335.ConstrainedCyclicToLoeb
import Erdos335.ConstrainedProfileComparison
import Erdos335.ConstrainedPhysicalProfileLimits
import Erdos335.LowGapPeriodicWindows
import Erdos335.PeriodicRefinementLabelClosureLoeb

/-!
# Periodic labels at prescribed small-error window starts

Private proof development. Verification status is recorded separately. The start sequence and both cyclic
length sequences are supplied by the caller. Dense removal constructs the
two actual-window models at those starts. A bounded null frame supplies a
label at the fixed factorial modulus, and physical window-count limits
identify its three profile vectors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open Erdos335.PeriodicRefinementLabelClosure
open scoped Pointwise ENNReal BigOperators

noncomputable section

namespace Erdos335.Loeb

instance factorial_neZero (D : ℕ) : NeZero D.factorial := ⟨Nat.factorial_ne_zero D⟩

local instance prescribedLabelLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

/-- The residue label is the absolute integer residue, including the start
phase. The reference length need not be divisible by the modulus. -/
theorem prescribed_window_profile_eq_limit
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : ℕ → ℕ) (q : ℕ → ℕ+) (hH : ∀ n, 0 < H n)
    (hHq : ∀ n, H n ≤ (q n : ℕ))
    (hgap : Tendsto (fun n => (((q n : ℕ) - H n : ℕ) : ℝ) / (q n : ℕ))
      atTop (𝓝 0))
    (S : Set ℕ) (start : ℕ → ℕ) (m : ℕ+)
    (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (r : ZMod (m : ℕ)) (v : ℝ)
    (hlimit : Tendsto (fun n => ((m : ℕ) : ℝ) *
      (((@cyclicWindow {k : ℕ | k ∈ S ∧ (k : ZMod (m : ℕ)) = r}
        (start n) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)) atTop (𝓝 v)) :
    actualWindowProfile U hU q m S start r = v := by
  have hactual := reference_window_profile_tendsto_of_actual_profile
    U hU H q hH hHq hgap S start m hd r
      (actualWindowProfile U hU q m S start r) rfl
  exact tendsto_nhds_unique hactual (hlimit.mono_left hU)

/-- Small convolution errors in both orientations give a genuine local
label and its strict-frame data for the limiting fine window profiles.
The ambient prefix-error hypotheses control all three actual window
masses. The natural bound and hence its factorial are fixed before any
window or ultrafilter is chosen. -/
theorem prescribed_small_error_window_has_label
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b))
    (hgap : a + b < gamma A B)
    (hlowA : ∀ η : ℝ, gamma A B - (a + b) < η →
      ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η)
    (hcapA : ∀ k : ℕ+, a + δA ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ))
    (hcapB : ∀ k : ℕ+, b + δB ≤ ((residues (k : ℕ) B).card : ℝ) / (k : ℕ))
    (D : ℕ)
    (hD : max (1 / δA) (max (1 / δB) (1 / (gamma A B - (a + b)))) ≤ (D : ℝ))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (N H start : ℕ → ℕ) (q : Bool → ℕ → ℕ+)
    (hH : ∀ n, 0 < H n) (hHtop : Tendsto H atTop atTop)
    (hHq : ∀ o n, H n ≤ (q o n : ℕ))
    (hqratio : ∀ o, Tendsto (fun n => ((q o n : ℕ) : ℝ) / H n) atTop (𝓝 1))
    (hdiv : ∀ o, ∀ k : ℕ+, ∀ᶠ n in atTop, (k : ℕ) ∣ (q o n : ℕ))
    (hstart : ∀ᶠ n in atTop, 0 < start n)
    (hinside : ∀ o, ∀ᶠ n in atTop, start n + (q o n : ℕ) ≤ N n)
    (hAerror : Tendsto (fun n => prefixError A a (N n) / H n) atTop (𝓝 0))
    (hBerror : Tendsto (fun n => prefixError B b (N n) / H n) atTop (𝓝 0))
    (hCerror : Tendsto (fun n => prefixError (A + B) (a + b) (N n) / H n)
      atTop (𝓝 0))
    (hperiod : ∀ o, Tendsto (fun n =>
      convolutionTranslationError (if o then B else A) (if o then A else B)
        (start n) (q o n : ℕ) / ((q o n : ℕ) : ℝ) ^ 2) atTop (𝓝 0))
    (vA vB vC : ZMod D.factorial → ℝ)
    (hprofileA : ∀ r, Tendsto (fun n => (D.factorial : ℝ) *
      (((@cyclicWindow {k : ℕ | k ∈ A ∧ (k : ZMod D.factorial) = r}
        (start n) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)) atTop (𝓝 (vA r)))
    (hprofileB : ∀ r, Tendsto (fun n => (D.factorial : ℝ) *
      (((@cyclicWindow {k : ℕ | k ∈ B ∧ (k : ZMod D.factorial) = r}
        (start n) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)) atTop (𝓝 (vB r)))
    (hprofileC : ∀ r, Tendsto (fun n => (D.factorial : ℝ) *
      (((@cyclicWindow {k : ℕ | k ∈ A + B ∧ (k : ZMod D.factorial) = r}
        (start n) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)) atTop (𝓝 (vC r))) :
    ∃ p : LocalProfile (residues D.factorial A) (residues D.factorial B)
        ((D.factorial : ℝ) * a) ((D.factorial : ℝ) * b),
      p.left = vA ∧ p.right = vB ∧ p.output = vC ∧
      ∃ label : LocalLabel (ZMod D.factorial), HasLabel p label ∧ LabelFrame p label := by
  classical
  let moving : Bool → Set ℕ := fun o => if o then B else A
  let other : Bool → Set ℕ := fun o => if o then A else B
  let movingMass : Bool → ℝ := fun o => if o then b else a
  let otherMass : Bool → ℝ := fun o => if o then a else b
  have hotherDensity (o : Bool) : HasDensity (other o) (otherMass o) := by
    cases o
    · exact hBdensity
    · exact hAdensity
  have hsumSet (o : Bool) : moving o + other o = A + B := by
    cases o
    · rfl
    · exact add_comm B A
  have hmovingError (o : Bool) : Tendsto
      (fun n => prefixError (moving o) (movingMass o) (N n) / H n) atTop (𝓝 0) := by
    cases o
    · exact hAerror
    · exact hBerror
  have hotherError (o : Bool) : Tendsto
      (fun n => prefixError (other o) (otherMass o) (N n) / H n) atTop (𝓝 0) := by
    cases o
    · exact hBerror
    · exact hAerror
  have houtputError (o : Bool) : Tendsto
      (fun n => prefixError (moving o + other o) (a + b) (N n) / H n)
        atTop (𝓝 0) := by
    simpa only [hsumSet o] using hCerror
  have hqtop (o : Bool) : Tendsto (fun n => (q o n : ℕ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hHtop
    exact Eventually.of_forall (hHq o)
  have hqgap (o : Bool) : Tendsto
      (fun n => (((q o n : ℕ) - H n : ℕ) : ℝ) / (q o n : ℕ)) atTop (𝓝 0) :=
    constrained_length_gap_of_ratio H (q o) (hHq o) (hqratio o)
  have hfinite (o : Bool) := exists_dense_cyclic_removal
    (moving o) (other o) (movingMass o) (otherMass o) (a + b) (hotherDensity o)
    N H (fun n => (q o n : ℕ)) start hH (hHq o) (hqtop o) hstart (hinside o)
    (hmovingError o) (houtputError o) (hperiod o)
  choose W P hsub hexhaust hWcount hPcount hCcount hWloss hPloss hspill using hfinite
  have hmodels (o : Bool) := constrained_cyclic_to_loeb
    U hU (moving o) (other o) (movingMass o) (otherMass o) (a + b)
    (hotherDensity o) N H start (q o) hH (hHq o) (hqtop o) (hinside o)
    (hmovingError o) (hotherError o) (W o) (P o) (hsub o) (hexhaust o)
    (hWcount o) (hPcount o) (hCcount o) (hspill o)
  choose E hEsub hEexhaust hWsub hWAE hP0 hmMoving hmOther hmC hmE hsum using hmodels
  have hmCActual (o : Bool) :
      (loebMeasure U hU (internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) :
          Set (ZMod (q o n : ℕ)))))).toReal = a + b := by
    simpa only [hsumSet o] using hmC o
  have hsumActual (o : Bool) :
      internalSet U (fun n => (W o n : Set (ZMod (q o n : ℕ)))) +
        internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
          ≤ᵐ[loebMeasure U hU] internalSet U
            (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) :
              Set (ZMod (q o n : ℕ)))) := by
    simpa only [hsumSet o] using hsum o
  obtain ⟨M₀, FA, FB, hFA, hFB, huniform⟩ := exists_uniform_low_gap_window_witnesses
    A B a b δA δB ha hb hδA hδB hAdensity hBdensity hCdensity hgap
      hlowA hcapA hcapB
  obtain ⟨o, h, hh, hframe, hcoverage⟩ := huniform U hU q hdiv hqtop H hH hHq hqgap
    start (fun o n => (W o n : Set (ZMod (q o n : ℕ)))) E hWsub hWAE
      (fun o => Eventually.of_forall (hEsub o)) hEexhaust hP0
        hmMoving hmOther hmCActual hmE hsumActual
  have hhD : (h : ℕ) ≤ D := by
    have hhReal : ((h : ℕ) : ℝ) ≤ (D : ℝ) := hh.trans hD
    exact_mod_cast hhReal
  have hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal = a := by
    cases o
    · exact hmMoving false
    · exact hmOther true
  have hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ)))))).toReal = b := by
    cases o
    · exact hmOther false
    · exact hmMoving true
  have hdivU (k : ℕ+) : ∀ᶠ n in U, (k : ℕ) ∣ (q o n : ℕ) :=
    (hdiv o k).filter_mono hU
  let M : ℕ+ := ⟨D.factorial, Nat.factorial_pos D⟩
  let p := actualLocalLabelProfile U hU (q o) (hqtop o) M (hdivU M)
    A B start a b hmA hmB (hmCActual o)
  have hlabeled : ∃ label : LocalLabel (ZMod (M : ℕ)),
      HasLabel p label ∧ LabelFrame p label := by
    exact actual_bounded_null_frame_has_label U hU (q o) hdivU (hqtop o)
      D h hhD A B start a b ha hb hmA hmB (hmCActual o) hgap hframe
  refine ⟨p, ?_, ?_, ?_, hlabeled⟩
  · funext r
    exact prescribed_window_profile_eq_limit U hU H (q o) hH (hHq o) (hqgap o)
      A start M (hdivU M) r (vA r) (hprofileA r)
  · funext r
    exact prescribed_window_profile_eq_limit U hU H (q o) hH (hHq o) (hqgap o)
      B start M (hdivU M) r (vB r) (hprofileB r)
  · funext r
    exact prescribed_window_profile_eq_limit U hU H (q o) hH (hHq o) (hqgap o)
      (A + B) start M (hdivU M) r (vC r) (hprofileC r)

end Erdos335.Loeb

end
