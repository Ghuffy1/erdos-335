import Erdos335.LoebInternalBohrPair
import Erdos335.ArcDensity

/-!
# An irrational arc from the standard restriction of a prefix character

The non-torsion premise is explicit. Its derivation from the critical-pair
hypotheses is a separate proof obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem standard_character_nat
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+)
    (χ : ∀ i, ZMod (q i : ℕ) →+ AddCircle (1 : ℝ)) (n : ℕ) :
    ultralimitAddHom U χ (productProjection (U : Filter ℕ)
      (fun i => (n : ZMod (q i : ℕ)))) =
      n • ultralimitAddHom U χ (productProjection (U : Filter ℕ)
        (fun i => (1 : ZMod (q i : ℕ)))) := by
  have hseq : (fun i => (n : ZMod (q i : ℕ))) =
      n • (fun i => (1 : ZMod (q i : ℕ))) := by
    funext i
    simp
  rw [hseq, map_nsmul, map_nsmul]

theorem prefix_arc_of_non_torsion_character
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+)
    (χ : ∀ i, ZMod (q i : ℕ) →+ AddCircle (1 : ℝ))
    (B : Set ℕ) (E : ℕ → Set ℕ) (y : ℝ)
    (hBpos : B ⊆ Set.Ioi 0) (hB : HasDensity B y) (hy : 0 < y) (hyone : y < 1)
    (hexhaust : ∀ n ∈ B, ∀ᶠ i in U, n ∈ E i)
    (x : AddCircle (1 : ℝ))
    (hcontain : internalSet U (fun i => ((↑) : ℕ → ZMod (q i : ℕ)) '' E i) ⊆
      (ultralimitAddHom U χ) ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 y)))
    (horder : addOrderOf (ultralimitAddHom U χ (productProjection (U : Filter ℕ)
      (fun i => (1 : ZMod (q i : ℕ))))) = 0) :
    ∃ θ start : ℝ, Irrational θ ∧ B ⊆ Proposed.closedArcPullback θ start y ∧
      HasDensity (Proposed.closedArcPullback θ start y \ B) 0 := by
  let z := ultralimitAddHom U χ (productProjection (U : Filter ℕ)
    (fun i => (1 : ZMod (q i : ℕ))))
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨start, hstart⟩ := QuotientAddGroup.mk_surjective x
  have hirr : Irrational θ := by
    have hdense : DenseRange (fun n : ℤ => n • (θ : AddCircle (1 : ℝ))) := by
      apply AddCircle.denseRange_zsmul_iff.mpr
      simpa only [hθ] using horder
    simpa only [div_one] using AddCircle.denseRange_zsmul_coe_iff.mp hdense
  have hsub : B ⊆ Proposed.closedArcPullback θ start y := by
    intro n hn
    have hmem : productProjection (U : Filter ℕ) (fun i => (n : ZMod (q i : ℕ))) ∈
        internalSet U (fun i => ((↑) : ℕ → ZMod (q i : ℕ)) '' E i) :=
      (hexhaust n hn).mono fun i hi => ⟨n, hi, rfl⟩
    obtain ⟨v, ⟨t, ht, rfl⟩, hv⟩ := hcontain hmem
    have hnchar : ultralimitAddHom U χ (productProjection (U : Filter ℕ)
        (fun i => (n : ZMod (q i : ℕ)))) = (((n : ℝ) * θ : ℝ) : AddCircle (1 : ℝ)) := by
      rw [standard_character_nat]
      change n • z = _
      rw [← hθ, Proposed.nsmul_coe_real]
    have heq : (((n : ℝ) * θ : ℝ) : AddCircle (1 : ℝ)) =
        ((start + t : ℝ) : AddCircle (1 : ℝ)) := by
      rw [← hnchar, AddCircle.coe_add, hstart]
      exact hv.symm
    obtain ⟨k, hk⟩ := NumStability.coe_eq_coe_iff_exists_int_sub_eq.mp heq
    exact ⟨hBpos hn, k, by linarith [ht.1], by linarith [ht.2]⟩
  have hzero : Negligible (B \ Proposed.closedArcPullback θ start y) := by
    apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
    rintro n ⟨hn, hnot⟩
    exact (hnot (hsub hn)).elim
  have hholes := (Proposed.closedArcPullback_hasDensity hirr start y hy hyone.le).sdiff_of_negligible_reverse
    hB hzero
  exact ⟨θ, start, hirr, hsub, by simpa only [sub_self] using hholes⟩

end Erdos335.Loeb

end
