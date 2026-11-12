import Erdos335.CircleArcContainment
import Erdos335.TranslatedCompactPairs

/-!
# Addition and erosion of embedded circle arcs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem subgroup_circle_arc_image
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (e : H ≃+ AddCircle (1 : ℝ))
    (S : Set (AddCircle (1 : ℝ))) :
    (Subtype.val : H → G) '' (e ⁻¹' S) = (H.subtype.comp e.symm.toAddMonoidHom) '' S := by
  ext z
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨e h, hh, by simp⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨e.symm s, by simpa using hs, rfl⟩

theorem embedded_closedArc_add
    {G : Type*} [AddCommGroup G] (f : AddCircle (1 : ℝ) →+ G)
    (u v : G) (x y : AddCircle (1 : ℝ)) (p r : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r) :
    (u +ᵥ (f '' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)))) +
      (v +ᵥ (f '' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)))) =
      (u + v) +ᵥ (f '' ((x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + r)))) := by
  rw [translate_pair_sum, ← Set.image_add f, translate_pair_sum,
    unitCircle_zero_closedArc_add p r hp hr]

theorem embedded_closedArc_erosion
    {G : Type*} [AddCommGroup G] (f : AddCircle (1 : ℝ) →+ G) (hf : Function.Injective f)
    (u v z : G) (x y : AddCircle (1 : ℝ)) (p r : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hsum : p + r < 1)
    (hsub : z +ᵥ (v +ᵥ (f '' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)))) ⊆
      (u + v) +ᵥ (f '' ((x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + r))))) :
    z ∈ u +ᵥ (f '' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p))) := by
  have hy : y ∈ y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r) :=
    ⟨0, ⟨0, ⟨le_rfl, hr⟩, by simp⟩, by simp⟩
  have hyimage : z + (v + f y) ∈ z +ᵥ
      (v +ᵥ (f '' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)))) :=
    ⟨v + f y, ⟨f y, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨w, ⟨c, hc, rfl⟩, heq⟩ := hsub hyimage
  have hvalue : u + f (c - y) = z := by
    rw [map_sub]
    change (u + v) + f c = z + (v + f y) at heq
    apply add_right_cancel
    calc
      (u + (f c - f y)) + (v + f y) = (u + v) + f c := by abel
      _ = z + (v + f y) := heq
  have hcircle : (c - y) +ᵥ (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)) ⊆
      (x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + r)) := by
    rintro t ⟨s, hs, rfl⟩
    have hpoint := hsub (show z + (v + f s) ∈ z +ᵥ
        (v +ᵥ (f '' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r)))) from
      ⟨v + f s, ⟨f s, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩)
    obtain ⟨w', ⟨d, hd, rfl⟩, heqd⟩ := hpoint
    have hfd : f d = f ((c - y) + s) := by
      rw [map_add]
      change (u + v) + f d = z + (v + f s) at heqd
      apply add_left_cancel (a := u + v)
      calc
        (u + v) + f d = z + (v + f s) := heqd
        _ = (u + v) + (f (c - y) + f s) := by rw [← hvalue]; abel
    have hdvalue : d = (c - y) + s := hf hfd
    simpa only [hdvalue, vadd_eq_add] using hd
  have hcI := unitCircle_translated_closedArc_erosion x y (c - y) p r hp hr hsum hcircle
  exact ⟨f (c - y), ⟨c - y, hcI, rfl⟩, hvalue⟩

end Erdos335.Loeb
