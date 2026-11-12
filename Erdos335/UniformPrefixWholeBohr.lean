import Erdos335.LoebBohrPairProfiles
import Erdos335.LoebQuasiFiniteProfiles
import Erdos335.LoebPeriodicPrefix
import Erdos335.LoebFiniteAugmentation

/-!
# Uniform positive prefix profiles force a whole Bohr terminal

Private proof development. Verification status is recorded separately.
The local terminal alternative is an explicit input. No global model
existence assertion is introduced here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance uniformPrefixLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem uniform_prefix_loeb_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (F : Set ℕ) (hF : F ⊆ Set.Ioi 0) (y : ℝ)
    (hdens : ∀ h : ℕ+, ∀ r : ZMod (h : ℕ), HasDensity (residueFiber F r) (y / (h : ℕ)))
    (P : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hP : P =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow F 0 (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    ∀ h : ℕ+, ∀ r : ZMod (h : ℕ), loebResidueProfile U hU q h P r = y := by
  intro h r
  rw [loebResidueProfile_eq_of_ae U hU q h P _ hP r]
  unfold loebResidueProfile
  rw [loeb_prefix_residue_measure_of_density U hU q hq h (hdiv h) F hF r
    (y / (h : ℕ)) (hdens h r)]
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  field_simp

theorem whole_bohr_modulus_one_of_uniform_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (W P : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (y : ℝ) (hy : 0 < y)
    (huniform : ∀ h : ℕ+, ∀ r : ZMod (h : ℕ), loebResidueProfile U hU q h P r = y)
    (d : InternalBohrPairData U hU q W P) : d.modulus = 1 := by
  classical
  let h := d.modulus
  let φ := finiteQuotient U d.residue
  have hid : naturalCyclicProjection h h = AddMonoidHom.id (ZMod (h : ℕ)) := by
    ext r
    rw [naturalCyclicProjection_val h h dvd_rfl, ZMod.natCast_zmod_val]
    rfl
  have hconstant (r : ZMod (h : ℕ)) : r = φ d.right_anchor := by
    by_contra hne
    have hp := (d.residue_profiles h (hdiv h) dvd_rfl).2 r
    change loebResidueProfile U hU q h P r =
      (if naturalCyclicProjection h h r = φ d.right_anchor then d.right_length else 0) at hp
    rw [hid, AddMonoidHom.id_apply, if_neg hne, huniform h r] at hp
    exact hy.ne' hp
  have hzero : (1 : ZMod (h : ℕ)) = 0 := (hconstant 1).trans (hconstant 0).symm
  have hdvd : (h : ℕ) ∣ 1 := (ZMod.natCast_eq_zero_iff 1 (h : ℕ)).mp (by simpa using hzero)
  have hh : (h : ℕ) = 1 := Nat.dvd_one.mp hdvd
  exact Subtype.ext hh

theorem not_quasiPeriodic_of_uniform_profiles
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (W P : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (y : ℝ) (hy : 0 < y) (hyone : y < 1)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (huniform : ∀ r : ZMod (h : ℕ), loebResidueProfile U hU q h P r = y)
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) W P)
    (hperiod : p.period = (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker) :
    False := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  have hconstant (r : ZMod (h : ℕ)) : r = φ p.right.anchor := by
    by_contra hne
    have hp := loeb_quasiPeriodic_residue_profile U hU q P p.period p.right h hd hperiod.symm r
    change loebResidueProfile U hU q h P r =
      (if r = φ p.right.anchor then (h : ℕ) * (loebMeasure U hU p.right.active).toReal
        else if r ∈ φ '' P then 1 else 0) at hp
    rw [if_neg hne, huniform r] at hp
    by_cases hr : r ∈ φ '' P
    · rw [if_pos hr] at hp
      exact hyone.ne hp
    · rw [if_neg hr] at hp
      exact hy.ne' hp
  have hφzero (g : G) : φ g = 0 := (hconstant (φ g)).trans (hconstant 0).symm
  have htop : p.period = ⊤ := by
    rw [hperiod]
    apply SetLike.ext
    intro g
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_top, iff_true]
    exact hφzero g
  have no_background (S : Set G)
      (r : QuasiPeriodicDecomposition (loebMeasure U hU) p.period S) :
      ¬ r.background.Nonempty := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := r.active_nonempty
    have hstep : g - a ∈ p.period := by rw [htop]; trivial
    have hactive : g ∈ r.active + (p.period : Set G) :=
      ⟨a, ha, g - a, hstep, by abel⟩
    exact Set.disjoint_left.mp r.separated hactive hg
  rcases p.nonempty_background with hleft | hright
  · exact no_background W p.left hleft
  · exact no_background P p.right hright

theorem whole_bohr_of_uniform_prefix_terminal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (F : Set ℕ) (hF : F ⊆ Set.Ioi 0) (y : ℝ) (hy : 0 < y) (hyone : y < 1)
    (hdens : ∀ h : ℕ+, ∀ r : ZMod (h : ℕ), HasDensity (residueFiber F r) (y / (h : ℕ)))
    (W P : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hP : P =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow F 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hterminal : Nonempty (InternalBohrPairData U hU q W P) ∨
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) W P,
        ∃ d : InternalBohrPairData U hU q p.left.active p.right.active,
          p.period = (finiteQuotient U d.residue).ker) :
    ∃ d : InternalBohrPairData U hU q W P, d.modulus = 1 := by
  have huniform := uniform_prefix_loeb_profiles U hU q hq hdiv F hF y hdens P hP
  rcases hterminal with hwhole | ⟨p, d, hp⟩
  · obtain ⟨d⟩ := hwhole
    exact ⟨d, whole_bohr_modulus_one_of_uniform_profiles U hU q hdiv W P y hy huniform d⟩
  · have hquotient : finiteQuotient U d.residue =
        finiteQuotient U (fun n => naturalCyclicProjection (q n) d.modulus) := by
      apply finiteQuotient_eq_of_eventually_natural
      · exact d.natural_residue.mono fun n hn => hn.2
      · exact (hdiv d.modulus).mono fun n hn k =>
          naturalCyclicProjection_natCast (q n) d.modulus hn k
    have hperiod : p.period =
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) d.modulus)).ker := by
      simpa only [hquotient] using hp
    exact False.elim (not_quasiPeriodic_of_uniform_profiles U hU q W P y hy hyone
      d.modulus (hdiv d.modulus) (huniform d.modulus) p hperiod)

end Erdos335.Loeb

end
