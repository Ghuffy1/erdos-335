import Erdos335.ArcDensity
import Erdos335.OrbitTranslateDensity

/-!
# Literal closed arcs and open orbit pullbacks

Private proof development. Verification status is recorded separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Proposed

theorem closedArcPullback_eq_positiveOrbitPullback (θ start y : ℝ) :
    closedArcPullback θ start y = positiveOrbitPullback θ
      ((start : AddCircle (1 : ℝ)) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 y)) := by
  ext n
  constructor
  · rintro ⟨hn, k, hlo, hhi⟩
    let t : ℝ := (n : ℝ) * θ - start - k
    refine ⟨hn, (t : AddCircle (1 : ℝ)), ⟨t, ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · dsimp only [t]
      linarith
    · dsimp only [t]
      linarith
    · change (start : AddCircle (1 : ℝ)) + (t : AddCircle (1 : ℝ)) =
        n • (θ : AddCircle (1 : ℝ))
      rw [nsmul_coe_real, ← AddCircle.coe_add]
      apply NumStability.coe_eq_coe_iff_exists_int_sub_eq.mpr
      refine ⟨-k, ?_⟩
      dsimp only [t]
      simp only [Int.cast_neg]
      ring
  · rintro ⟨hn, v, ⟨t, ht, rfl⟩, hphase⟩
    change (start : AddCircle (1 : ℝ)) + (t : AddCircle (1 : ℝ)) =
      n • (θ : AddCircle (1 : ℝ)) at hphase
    rw [nsmul_coe_real, ← AddCircle.coe_add] at hphase
    obtain ⟨k, hk⟩ := NumStability.coe_eq_coe_iff_exists_int_sub_eq.mp hphase.symm
    exact ⟨hn, k, by linarith [ht.1], by linarith [ht.2]⟩

theorem closedArcPullback_openOrbit_equivalent
    (θ start y : ℝ) (hθ : Irrational θ) :
    DensityEquivalent (closedArcPullback θ start y)
      (positiveOrbitPullback θ
        ((start : AddCircle (1 : ℝ)) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 y))) := by
  let O := positiveOrbitPullback θ
    ((start : AddCircle (1 : ℝ)) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 y))
  have hsubset : O ⊆ closedArcPullback θ start y := by
    rintro n ⟨hn, v, ⟨t, ht, rfl⟩, hphase⟩
    rw [closedArcPullback_eq_positiveOrbitPullback]
    exact ⟨hn, (t : AddCircle (1 : ℝ)), ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, hphase⟩
  have hboundary := (irrational_orbitPoint_negligible hθ (start : AddCircle (1 : ℝ))).union
    (irrational_orbitPoint_negligible hθ ((start + y : ℝ) : AddCircle (1 : ℝ)))
  constructor
  · apply hboundary.mono
    rintro n ⟨hnC, hnO⟩
    rw [closedArcPullback_eq_positiveOrbitPullback] at hnC
    obtain ⟨hn, v, ⟨t, ht, rfl⟩, hphase⟩ := hnC
    change (start : AddCircle (1 : ℝ)) + (t : AddCircle (1 : ℝ)) =
      n • (θ : AddCircle (1 : ℝ)) at hphase
    by_cases htzero : t = 0
    · apply Or.inl
      change n • (θ : AddCircle (1 : ℝ)) = (start : AddCircle (1 : ℝ))
      simpa only [htzero, AddCircle.coe_zero, add_zero] using hphase.symm
    by_cases hty : t = y
    · apply Or.inr
      change n • (θ : AddCircle (1 : ℝ)) = ((start + y : ℝ) : AddCircle (1 : ℝ))
      simpa only [hty, AddCircle.coe_add] using hphase.symm
    exact False.elim (hnO ⟨hn, (t : AddCircle (1 : ℝ)),
      ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm htzero), lt_of_le_of_ne ht.2 hty⟩, rfl⟩, hphase⟩)
  · apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
    rintro n ⟨hnO, hnC⟩
    exact (hnC (hsubset hnO)).elim

theorem filled_arc_openOrbit_equivalent
    (θ start y : ℝ) (hθ : Irrational θ) (F : Set ℕ)
    (hFsub : F ⊆ closedArcPullback θ start y)
    (hholes : Negligible (closedArcPullback θ start y \ F)) :
    DensityEquivalent F (positiveOrbitPullback θ
      ((start : AddCircle (1 : ℝ)) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 y))) := by
  have hFC : DensityEquivalent F (closedArcPullback θ start y) := by
    refine ⟨?_, hholes⟩
    apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
    rintro n ⟨hnF, hnC⟩
    exact (hnC (hFsub hnF)).elim
  exact hFC.trans (closedArcPullback_openOrbit_equivalent θ start y hθ)

end Erdos335.Proposed

end
