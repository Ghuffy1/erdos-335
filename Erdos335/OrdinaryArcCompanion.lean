import Erdos335.ArcOrbitPullback
import Erdos335.OrbitCarrierMeasure
import Erdos335.OrbitClosureOpenSum
import Erdos335.CircleOpenArcCompanion

/-!
# Ordinary-density measure bounds for the companion of a filled arc

Private proof development. Verification status is recorded separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Proposed

local instance ordinaryCompanionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  Loeb.loebMeasurableSpace U

theorem filled_arc_companion_measure_bounds
    (θ startF x y : ℝ) (hθ : Irrational θ) (E F : Set ℕ)
    (hE : HasDensity E x) (hsum : HasDensity (E + F) (x + y))
    (hFsub : F ⊆ closedArcPullback θ startF y)
    (hFholes : Negligible (closedArcPullback θ startF y \ F)) :
    let K := closure ((fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) '' E)
    let J := (startF : AddCircle (1 : ℝ)) +ᵥ
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 y)
    x ≤ (volume K).toReal ∧ (volume (K + J)).toReal ≤ x + y := by
  let K := closure ((fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) '' E)
  let J := (startF : AddCircle (1 : ℝ)) +ᵥ
    (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 y)
  have hJ : IsOpen J := by
    change IsOpen ((startF : AddCircle (1 : ℝ)) +ᵥ
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 y))
    rw [Loeb.vadd_set_eq_neg_preimage]
    exact (QuotientAddGroup.isOpenMap_coe _ (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) y))).preimage
      (continuous_const.add continuous_id)
  have hFmodel : DensityEquivalent F (positiveOrbitPullback θ J) :=
    filled_arc_openOrbit_equivalent θ startF y hθ F hFsub hFholes
  have hlower : x ≤ (volume K).toReal := by
    apply density_le_closed_orbit_carrier_measure θ hθ E x hE K isClosed_closure
    intro n hn
    exact subset_closure ⟨n, hn, rfl⟩
  have hfinite (T : Finset ℕ) (hT : (T : Set ℕ) ⊆ E) :
      (volume (⋃ n ∈ T, n • (θ : AddCircle (1 : ℝ)) +ᵥ J)).toReal ≤ x + y := by
    have hopen : IsOpen (⋃ n ∈ T, n • (θ : AddCircle (1 : ℝ)) +ᵥ J) := by
      apply isOpen_iUnion
      intro n
      apply isOpen_iUnion
      intro _
      rw [Loeb.vadd_set_eq_neg_preimage]
      exact hJ.preimage (continuous_const.add continuous_id)
    exact open_orbit_measure_le_density_of_negligible_excess θ hθ _ hopen
      (E + F) (x + y) hsum
      (positiveOrbitPullback_finite_translates_sdiff_sum_negligible θ J E F hFmodel T hT)
  have hupper : (volume (K + J)).toReal ≤ x + y :=
    volume_orbit_closure_add_open_toReal_le θ E J hJ (x + y) hfinite
  exact ⟨hlower, hupper⟩

theorem ordinary_filled_arc_companion
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (θ startF x y : ℝ) (hθ : Irrational θ) (E F : Set ℕ)
    (hEpos : E ⊆ Ioi 0) (hx : 0 < x) (hy : 0 < y) (hxy : x + y < 1)
    (hE : HasDensity E x) (hsum : HasDensity (E + F) (x + y))
    (hFsub : F ⊆ closedArcPullback θ startF y)
    (hFholes : Negligible (closedArcPullback θ startF y \ F)) :
    ∃ startE : ℝ, E ⊆ closedArcPullback θ startE x ∧
      HasDensity (closedArcPullback θ startE x \ E) 0 := by
  let K := closure ((fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) '' E)
  have hK : IsCompact K := isClosed_closure.isCompact
  obtain ⟨hKlower, hSupper⟩ :=
    filled_arc_companion_measure_bounds θ startF x y hθ E F hE hsum hFsub hFholes
  obtain ⟨c, hKsub, _⟩ := Loeb.unitCircle_compact_openArc_companion U hU q φ hφ hsurj
    K hK (startF : AddCircle (1 : ℝ)) x y hx hy hxy hKlower hSupper
  obtain ⟨startE, hstartE⟩ := QuotientAddGroup.mk_surjective c
  have hEsub : E ⊆ closedArcPullback θ startE x := by
    intro n hn
    have hnK : n • (θ : AddCircle (1 : ℝ)) ∈ K := subset_closure ⟨n, hn, rfl⟩
    have hnArc := hKsub hnK
    rw [closedArcPullback_eq_positiveOrbitPullback]
    refine ⟨hEpos hn, ?_⟩
    simpa only [hstartE] using hnArc
  have hzero : Negligible (E \ closedArcPullback θ startE x) := by
    apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
    rintro n ⟨hn, hnot⟩
    exact (hnot (hEsub hn)).elim
  have hholes := (closedArcPullback_hasDensity hθ startE x hx (by linarith)).sdiff_of_negligible_reverse
    hE hzero
  exact ⟨startE, hEsub, by simpa only [sub_self] using hholes⟩

end Erdos335.Proposed

end
