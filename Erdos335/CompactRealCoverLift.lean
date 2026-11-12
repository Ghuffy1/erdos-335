import Erdos335.CompactCircleCover
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Convex.Contractible

/-!
# Lifting the real line through a finite compact circle cover
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology

namespace Erdos335.Loeb

theorem exists_real_hom_lift_of_circle_cover
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [ConnectedSpace G] [T2Space G]
    (φ : G →+ AddCircle (1 : ℝ)) (hφ : Continuous φ) (hne : φ ≠ 0)
    [Finite φ.ker] :
    ∃ f : ℝ →+ G, Continuous f ∧ ∀ x : ℝ, φ (f x) = (x : AddCircle (1 : ℝ)) := by
  have hcover := isCoveringMap_of_finite_circle_kernel φ hφ hne
  let q : C(ℝ, AddCircle (1 : ℝ)) := ⟨fun x => (x : AddCircle (1 : ℝ)),
    continuous_quotient_mk'⟩
  obtain ⟨F, ⟨hzero, hlift⟩, _⟩ := hcover.existsUnique_continuousMap_lifts q 0 0 (by simp [q])
  have hpoint (x : ℝ) : φ (F x) = (x : AddCircle (1 : ℝ)) := congrFun hlift x
  have hadd : ∀ x y : ℝ, F (x + y) = F x + F y := by
    have heq : (fun p : ℝ × ℝ => F (p.1 + p.2)) = (fun p : ℝ × ℝ => F p.1 + F p.2) :=
      hcover.eq_of_comp_eq (F.continuous.comp (continuous_fst.add continuous_snd))
        ((F.continuous.comp continuous_fst).add (F.continuous.comp continuous_snd))
        (by funext p; simp only [Function.comp_apply, map_add, hpoint, QuotientAddGroup.mk_add])
        (0, 0) (by simp [hzero])
    intro x y
    exact congrFun heq (x, y)
  let f : ℝ →+ G := { toFun := F, map_zero' := hzero, map_add' := hadd }
  exact ⟨f, F.continuous, hpoint⟩

theorem real_hom_lift_of_circle_cover_surjective
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [ConnectedSpace G] [T2Space G]
    (φ : G →+ AddCircle (1 : ℝ)) (hφ : Continuous φ) (hne : φ ≠ 0)
    [Finite φ.ker] (f : ℝ →+ G) (hf : Continuous f)
    (hlift : ∀ x : ℝ, φ (f x) = (x : AddCircle (1 : ℝ))) :
    Function.Surjective f := by
  have hcover := isCoveringMap_of_finite_circle_kernel φ hφ hne
  have hcomp : φ ∘ f = ((↑) : ℝ → AddCircle (1 : ℝ)) := funext hlift
  have hfLocal : IsLocalHomeomorph f := by
    apply IsLocalHomeomorph.of_comp (g := φ) (f := f) _ hcover.isLocalHomeomorph hf
    rw [hcomp]
    exact AddCircle.isLocalHomeomorph_coe (1 : ℝ)
  let H : OpenAddSubgroup G :=
    { toAddSubgroup := f.range
      isOpen' := by
        change IsOpen (Set.range f)
        simpa only [Set.image_univ] using hfLocal.isOpenMap Set.univ isOpen_univ }
  have hH : (H : Set G) = Set.univ := H.isClopen.eq_univ ⟨0, H.zero_mem⟩
  intro y
  have hy : y ∈ H := by
    change y ∈ (H : Set G)
    rw [hH]
    trivial
  exact hy

end Erdos335.Loeb
