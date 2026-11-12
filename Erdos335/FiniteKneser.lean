import Erdos335.Residues
import MiscYD.AddCombi.Kneser.Kneser

/-!
# Finite Kneser consequences for the full Erdős 335 proof

The general Kneser theorem is imported from the exact, attributed MiscYD
formalization. This file proves the strict finite completion lemma used in the
local inverse and periodic-output reductions of the proposed full solution.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Erdos335.FiniteKneser

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
variable {A B U : Finset G} {x : G}

lemma subset_add_stabilizer_right (A : Finset G) {H : Finset G} (hH : 0 ∈ H) :
    A ⊆ A + H := by
  intro a ha
  exact Finset.mem_add.mpr ⟨a, ha, 0, hH, add_zero a⟩

/-- Below the sum of input sizes, the saturated Kneser bound is exact. -/
theorem critical_card_identity (hA : A.Nonempty) (hB : B.Nonempty)
    (hsmall : (A + B).card < A.card + B.card) :
    (A + (A + B).addStab).card + (B + (A + B).addStab).card =
      (A + B).card + (A + B).addStab.card := by
  have hzero : (0 : G) ∈ (A + B).addStab :=
    Finset.zero_mem_addStab.mpr (hA.add hB)
  have hAl := Finset.card_le_card (subset_add_stabilizer_right A hzero)
  have hBl := Finset.card_le_card (subset_add_stabilizer_right B hzero)
  have hk := Finset.add_kneser A B
  apply le_antisymm hk
  by_contra h
  have hstrict : (A + (A + B).addStab).card + (B + (A + B).addStab).card <
      (A + B).card + (A + B).addStab.card := by omega
  have hsharp := Finset.add_strict_kneser A B hstrict
  omega

/-- A new point whose translates stay inside a critical sum lies in its saturated input. -/
theorem exact_completion_mem_saturation (hA : A.Nonempty) (hB : B.Nonempty)
    (hsmall : (A + B).card < A.card + B.card)
    (hx : ∀ b ∈ B, x + b ∈ A + B) : x ∈ A + (A + B).addStab := by
  classical
  have hzero : (0 : G) ∈ (A + B).addStab :=
    Finset.zero_mem_addStab.mpr (hA.add hB)
  have heq : insert x A + B = A + B := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hy
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hx b hb
      · exact Finset.add_mem_add ha hb
    · exact Finset.add_subset_add (Finset.subset_insert x A) (Finset.Subset.refl B)
  by_contra hnot
  have hsub : A + (A + B).addStab ⊆ insert x A + (A + B).addStab :=
    Finset.add_subset_add (Finset.subset_insert x A) (Finset.Subset.refl _)
  have hnew : x ∈ insert x A + (A + B).addStab :=
    Finset.mem_add.mpr ⟨x, Finset.mem_insert_self x A, 0, hzero, add_zero x⟩
  have hproper : A + (A + B).addStab ⊂ insert x A + (A + B).addStab :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hnot (he.symm ▸ hnew)⟩
  have hcard := Finset.card_lt_card hproper
  have hk := Finset.add_kneser (insert x A) B
  rw [heq] at hk
  have hc := critical_card_identity hA hB hsmall
  omega

lemma translate_coset_disjoint (hA : A.Nonempty) (hB : B.Nonempty)
    {b : G} (hmissing : x + b ∉ A + B) :
    Disjoint (x +ᵥ (b +ᵥ (A + B).addStab)) (A + B) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzV
  obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp hz
  obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hy
  have hs : h +ᵥ (A + B) = A + B := (Finset.mem_addStab (hA.add hB)).mp hh
  have hz' : h + (x + b) ∈ h +ᵥ (A + B) := by
    rw [hs]
    simpa only [vadd_eq_add, add_assoc, add_comm, add_left_comm] using hzV
  obtain ⟨v, hv, heq⟩ := Finset.mem_vadd_finset.mp hz'
  have hvEq : v = x + b := by
    simpa only [vadd_eq_add, add_right_inj] using heq
  exact hmissing (hvEq ▸ hv)

/-- Every point compatible with the containing set lies in the original saturated input. -/
theorem completion_mem_saturation (hA : A.Nonempty) (hB : B.Nonempty)
    (hVU : A + B ⊆ U) (hsmall : U.card < A.card + B.card)
    (hx : ∀ b ∈ B, x + b ∈ U) : x ∈ A + (A + B).addStab := by
  classical
  have hsmallV : (A + B).card < A.card + B.card :=
    lt_of_le_of_lt (Finset.card_le_card hVU) hsmall
  have hzero : (0 : G) ∈ (A + B).addStab :=
    Finset.zero_mem_addStab.mpr (hA.add hB)
  by_contra hxout
  have hmissing : ∃ b ∈ B, x + b ∉ A + B := by
    by_contra h
    push Not at h
    exact hxout (exact_completion_mem_saturation hA hB hsmallV h)
  obtain ⟨b, hb, hmissing⟩ := hmissing
  let H := (A + B).addStab
  let C := b +ᵥ H
  have hCsub : C ⊆ B + H := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hy
    exact Finset.add_mem_add hb hh
  have hBsub : B ⊆ B + H := subset_add_stabilizer_right B hzero
  have hCsize : C.card = H.card := Finset.card_vadd_finset b H
  have hholes : (C \ B).card ≤ (B + H).card - B.card := by
    rw [← Finset.card_sdiff_of_subset hBsub]
    exact Finset.card_le_card (Finset.sdiff_subset_sdiff hCsub (Finset.Subset.refl B))
  have hpartition : (B ∩ C).card + (C \ B).card = C.card := by
    rw [Finset.inter_comm]
    exact Finset.card_inter_add_card_sdiff C B
  have hdisjoint : Disjoint (x +ᵥ C) (A + B) :=
    translate_coset_disjoint hA hB hmissing
  have hcovered : x +ᵥ (B ∩ C) ⊆ U \ (A + B) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_vadd_finset.mp hy
    have hzB : z ∈ B := (Finset.mem_inter.mp hz).1
    have hzC : z ∈ C := (Finset.mem_inter.mp hz).2
    refine Finset.mem_sdiff.mpr ⟨hx z hzB, ?_⟩
    exact Finset.disjoint_left.mp hdisjoint
      (Finset.vadd_mem_vadd_finset hzC) 
  have hfit : (B ∩ C).card ≤ U.card - (A + B).card := by
    rw [← Finset.card_vadd_finset x (B ∩ C), ← Finset.card_sdiff_of_subset hVU]
    exact Finset.card_le_card hcovered
  have hidentity := critical_card_identity hA hB hsmallV
  have hAl := Finset.card_le_card (subset_add_stabilizer_right A hzero)
  have hBl := Finset.card_le_card hBsub
  have hVl := Finset.card_le_card hVU
  change A.card ≤ (A + H).card at hAl
  change (A + H).card + (B + H).card = (A + B).card + H.card at hidentity
  omega

/-- Strict finite completion lemma from the proposed full proof, for every abelian group. -/
theorem strict_completion (hA : A.Nonempty) (hB : B.Nonempty)
    (hVU : A + B ⊆ U) (hsmall : U.card < A.card + B.card)
    {x y : G} (hx : ∀ b ∈ B, x + b ∈ U) (hy : ∀ a ∈ A, a + y ∈ U) :
    x + y ∈ A + B := by
  have hxP := completion_mem_saturation hA hB hVU hsmall hx
  have hyQ : y ∈ B + (A + B).addStab := by
    have hy' : ∀ a ∈ A, y + a ∈ U := by
      intro a ha
      simpa only [add_comm] using hy a ha
    have h' := completion_mem_saturation hB hA (by simpa only [add_comm] using hVU)
      (by omega) hy'
    simpa only [add_comm] using h'
  have hsum := Finset.add_mem_add hxP hyQ
  have heq : (A + (A + B).addStab) + (B + (A + B).addStab) = A + B := by
    rw [add_add_add_comm, Finset.addStab_add_addStab, Finset.add_addStab]
  rwa [heq] at hsum

def completionSet (B U : Finset G) : Set G := {x | ∀ b ∈ B, x + b ∈ U}

/-- The exact set-valued completion statement used by the inverse reductions. -/
theorem sum_completions_subset (hA : A.Nonempty) (hB : B.Nonempty)
    (hVU : A + B ⊆ U) (hsmall : U.card < A.card + B.card) :
    completionSet B U + completionSet A U ⊆ (A + B : Finset G) := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  apply strict_completion hA hB hVU hsmall hx
  intro a ha
  simpa only [add_comm] using hy a ha

/-- Larger literal supports still add into the original critical sum. -/
theorem extended_support_sum_subset {P Q S T : Finset G}
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hcore : P + Q ⊆ U)
    (hleft : S + Q ⊆ U) (hright : P + T ⊆ U)
    (hsmall : U.card < P.card + Q.card) : S + T ⊆ P + Q := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  apply strict_completion hP hQ hcore hsmall
  · intro q hq
    exact hleft (Finset.add_mem_add hx hq)
  · intro p hp
    exact hright (Finset.add_mem_add hp hy)

/-- The strict bound is essential, already for residues modulo five. -/
theorem equality_boundary_counterexample :
    let A : Finset (ZMod 5) := {0, 1}
    let B : Finset (ZMod 5) := {0, 2}
    let U : Finset (ZMod 5) := {0, 1, 2, 3}
    A + B ⊆ U ∧ U.card = A.card + B.card ∧
      (∀ b ∈ B, 3 + b ∈ U) ∧ (∀ a ∈ A, a + 1 ∈ U) ∧ (3 + 1 : ZMod 5) ∉ A + B := by
  decide

end Erdos335.FiniteKneser
