import Erdos335.ConstrainedCyclicToLoeb
import Erdos335.HighGapFixedScaleProfiles
import Erdos335.LoebOrdinaryPrefixProfiles

/-!
# One positive local profile realizing all ordinary residue densities

Private proof development. Verification status is recorded separately. Ordinary residue densities identify the
zero-prefix profiles in one actual paired High model at every modulus.
Its literal support and all-refinement formulas are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance ordinaryReferenceLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_high_gap_profile_of_ordinary_residue_densities
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b))
    (hgap : a + b < gamma A B)
    (hhighA : gamma A B < a + b + δA)
    (hhighB : gamma A B < a + b + δB)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (N L V H : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (hHpos : ∀ s, 0 < H s) (hH : Tendsto H atTop atTop)
    (hLH : Tendsto (fun s => (L s : ℝ) / H s) atTop (𝓝 0))
    (hHV : Tendsto (fun s => (H s : ℝ) / V s) atTop (𝓝 0))
    (hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (mA : IntermediateFourierModel (A.indicator (fun _ => (1 : ℝ))) N L V)
    (mB : IntermediateFourierModel (B.indicator (fun _ => (1 : ℝ))) N L V)
    (hAerror : Tendsto (fun s => prefixError A a (N s) / H s) atTop (𝓝 0))
    (hBerror : Tendsto (fun s => prefixError B b (N s) / H s) atTop (𝓝 0))
    (hCerror : Tendsto (fun s => prefixError (A + B) (a + b) (N s) / H s)
      atTop (𝓝 0))
    (fA fB : NaturalResidueProfile)
    (hfA : ∀ (m : ℕ+) (r : ZMod (m : ℕ)), HasDensity {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
      (fA m r / (m : ℕ)))
    (hfB : ∀ (m : ℕ+) (r : ZMod (m : ℕ)), HasDensity {n : ℕ | n ∈ B ∧ (n : ZMod (m : ℕ)) = r}
      (fB m r / (m : ℕ))) :
    ∃ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 ∧
      ∃ output : NaturalResidueProfile,
      ∃ p : LocalPositiveResidueProfile h A B a b fA fB output,
        p.movingSupport = residues (h : ℕ) A := by
  classical
  let left : Bool → Set ℕ := fun o => if o then B else A
  let right : Bool → Set ℕ := fun o => if o then A else B
  let leftMass : Bool → ℝ := fun o => if o then b else a
  let rightMass : Bool → ℝ := fun o => if o then a else b
  let outputMass : Bool → ℝ := fun _ => a + b
  have hrightDensity : ∀ o, HasDensity (right o) (rightMass o) := by
    intro o
    cases o
    · exact hBdensity
    · exact hAdensity
  have hmodelsFourier : ∀ o,
      IntermediateFourierModel ((left o).indicator (fun _ => (1 : ℝ))) N L V := by
    intro o
    cases o
    · exact mA
    · exact mB
  have hleftError : ∀ o,
      Tendsto (fun s => prefixError (left o) (leftMass o) (N s) / H s)
        atTop (𝓝 0) := by
    intro o
    cases o
    · exact hAerror
    · exact hBerror
  have hrightError : ∀ o,
      Tendsto (fun s => prefixError (right o) (rightMass o) (N s) / H s)
        atTop (𝓝 0) := by
    intro o
    cases o
    · exact hBerror
    · exact hAerror
  have hsumSet (o : Bool) : left o + right o = A + B := by
    cases o
    · rfl
    · exact add_comm B A
  have houtputError : ∀ o,
      Tendsto (fun s => prefixError (left o + right o) (outputMass o) (N s) / H s)
        atTop (𝓝 0) := by
    intro o
    simpa only [hsumSet o, outputMass] using hCerror
  let S : ℕ → Finset ℕ := fun s => Finset.range (N s)
  have hS : ∀ s, S s ⊆ Finset.range (N s) := by
    intro s k hk
    exact hk
  have hcard : ∀ᶠ s in atTop, (1 : ℝ) ≤ ((S s).card : ℝ) / N s := by
    apply Eventually.of_forall
    intro s
    have hNz : (N s : ℝ) ≠ 0 := by exact_mod_cast (hN s).ne'
    simp only [S, Finset.card_range, div_self hNz, le_refl]
  obtain ⟨n, q, _, _, hmodels⟩ := exists_constrained_cyclic_models
    left right leftMass rightMass outputMass hrightDensity N L V H hN hHpos hH
      hLH hHV hHN hmodelsFourier hleftError houtputError S hS 1 zero_lt_one hcard
  let start : ℕ → ℕ := fun s => n s + 3 * H s
  have hHq (o : Bool) := (hmodels o).1
  have hqtop (o : Bool) := (hmodels o).2.1
  have hqgap (o : Bool) := (hmodels o).2.2.1
  have hqdiv (o : Bool) := (hmodels o).2.2.2.1
  have hinside (o : Bool) := (hmodels o).2.2.2.2.1
  have hfinite (o : Bool) := (hmodels o).2.2.2.2.2
  choose D P hsub hexhaust hDcount hPcount hCcount hspill using hfinite
  have hLoeb (o : Bool) := constrained_cyclic_to_loeb U hU (left o) (right o)
    (leftMass o) (rightMass o) (a + b) (hrightDensity o) N H start (q o)
      hHpos (hHq o) (hqtop o) (hinside o) (hleftError o) (hrightError o)
        (D o) (P o) (hsub o) (hexhaust o) (hDcount o) (hPcount o)
          (hCcount o) (hspill o)
  choose E hEsub hEexhaust hDsub hDAE hP0 hmMoving hmOther hmC hmE hsum using hLoeb
  have hmCActual (o : Bool) :
      (loebMeasure U hU (internalSet U
        (fun s => (cyclicWindow (A + B) (start s) (q o s : ℕ) :
          Set (ZMod (q o s : ℕ)))))).toReal = a + b := by
    simpa only [hsumSet o] using hmC o
  have hsumActual (o : Bool) :
      internalSet U (fun s => (D o s : Set (ZMod (q o s : ℕ)))) +
        internalSet U (fun s => ((↑) : ℕ → ZMod (q o s : ℕ)) '' E o s)
          ≤ᵐ[loebMeasure U hU] internalSet U
            (fun s => (cyclicWindow (A + B) (start s) (q o s : ℕ) :
              Set (ZMod (q o s : ℕ)))) := by
    simpa only [hsumSet o] using hsum o
  have hdivAtTop : ∀ o, ∀ m : ℕ+, ∀ᶠ s in atTop, (m : ℕ) ∣ (q o s : ℕ) :=
    fun o m => hqdiv o (m : ℕ) m.pos
  have hdivU : ∀ o, ∀ m : ℕ+, ∀ᶠ s in U, (m : ℕ) ∣ (q o s : ℕ) :=
    fun o m => (hdivAtTop o m).filter_mono hU
  have hCagree (m : ℕ+) (r : ZMod (m : ℕ)) :
      actualWindowProfile U hU (q false) m (A + B) start r =
        actualWindowProfile U hU (q true) m (A + B) start r :=
    constrained_actual_window_profiles_agree U hU (A + B) start H (q false) (q true)
      hHpos (hHq false) (hHq true) (hqgap false) (hqgap true) m
        (hdivAtTop false m) (hdivAtTop true m) r
  obtain ⟨h, hbound, p, _, hSA, _, _, _, hprofiles⟩ := exists_high_gap_paired_profiles
    U hU q hdivU hqtop A B start a b δA δB ha hb
      hAdensity hBdensity hCdensity hgap hhighA hhighB hcapA hcapB
        (fun o s => (D o s : Set (ZMod (q o s : ℕ)))) E hDsub hDAE
          (fun o => Eventually.of_forall (hEsub o)) hEexhaust hP0
            hmMoving hmOther hmCActual hmE hsumActual hCagree
  have hprefixA (m : ℕ+) (r : ZMod (m : ℕ)) :
      actualWindowProfile U hU (q true) m A (fun _ => 0) r = fA m r :=
    actual_zero_prefix_profile_of_density U hU (q true) (hqtop true) m
      (hdivU true m) A r (fA m r) (hfA m r)
  have hprefixB (m : ℕ+) (r : ZMod (m : ℕ)) :
      actualWindowProfile U hU (q false) m B (fun _ => 0) r = fB m r :=
    actual_zero_prefix_profile_of_density U hU (q false) (hqtop false) m
      (hdivU false m) B r (fB m r) (hfB m r)
  let pglobal : LocalPositiveResidueProfile h A B a b fA fB
      (fun m r => actualWindowProfile U hU (q false) m (A + B) start r) :=
    { p with
      moving_profile := by
        intro m hm r
        exact (hprefixA m r).symm.trans
          (((hprofiles m hm).1 r).symm.trans (p.moving_profile m hm r))
      prefix_profile := by
        intro m hm r
        exact (hprefixB m r).symm.trans (p.prefix_profile m hm r)
    }
  exact ⟨h, hbound, _, pglobal, hSA⟩

end Erdos335.Loeb

end

