import Erdos335.FiniteKneser
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Literal residue maps for finite cyclic quotients

The quotient generator is the image of one. This fixes the correspondence
with ordinary integer residues when a stabilizer is factored out.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Erdos335

theorem exists_natural_cyclic_quotient (q : ℕ+) (K : AddSubgroup (ZMod (q : ℕ))) :
    ∃ (h : ℕ+) (π : ZMod (q : ℕ) →+ ZMod (h : ℕ)),
      (h : ℕ) = K.index ∧ (h : ℕ) ∣ (q : ℕ) ∧ Function.Surjective π ∧ π.ker = K ∧
        ∀ n : ℕ, π (n : ZMod (q : ℕ)) = (n : ZMod (h : ℕ)) := by
  classical
  let Q := ZMod (q : ℕ) ⧸ K
  let f : ZMod (q : ℕ) →+ Q := QuotientAddGroup.mk' K
  have hf : Function.Surjective f := QuotientAddGroup.mk'_surjective K
  have hg : ∀ x : Q, x ∈ AddSubgroup.zmultiples (f 1) := by
    intro x
    obtain ⟨y, rfl⟩ := hf x
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
    refine ⟨n, ?_⟩
    change n • f 1 = f (n : ZMod (q : ℕ))
    rw [← map_zsmul]
    simp
  have hindex : 0 < K.index := by
    change 0 < Nat.card Q
    exact Nat.card_pos
  let h : ℕ+ := ⟨K.index, hindex⟩
  let e : ZMod (h : ℕ) ≃+ Q := zmodAddEquivOfGenerator hg rfl
  let π : ZMod (q : ℕ) →+ ZMod (h : ℕ) := e.symm.toAddMonoidHom.comp f
  have hπ : Function.Surjective π := e.symm.surjective.comp hf
  refine ⟨h, π, rfl, ?_, hπ, ?_, ?_⟩
  · change K.index ∣ (q : ℕ)
    simpa only [Nat.card_zmod] using K.index_dvd_card
  · ext x
    change e.symm (f x) = 0 ↔ x ∈ K
    rw [AddEquiv.symm_apply_eq]
    simp only [map_zero]
    exact QuotientAddGroup.eq_zero_iff x
  · intro n
    change e.symm (f (n : ZMod (q : ℕ))) = (n : ZMod (h : ℕ))
    rw [AddEquiv.symm_apply_eq]
    have he1 : e 1 = f 1 := zmodAddEquivOfGenerator_apply_one hg rfl
    have he : e (n : ZMod (h : ℕ)) = (n : ℕ) • f 1 := by
      calc
        e (n : ZMod (h : ℕ)) = e (n • (1 : ZMod (h : ℕ))) := by simp
        _ = n • e 1 := by rw [map_nsmul]
        _ = n • f 1 := by rw [he1]
    rw [he, ← map_nsmul]
    simp

theorem residues_image_of_natCast (q h : ℕ+)
    (π : ZMod (q : ℕ) →+ ZMod (h : ℕ))
    (hπ : ∀ n : ℕ, π (n : ZMod (q : ℕ)) = (n : ZMod (h : ℕ))) (A : Set ℕ) :
    (residues (q : ℕ) A).image π = residues (h : ℕ) A := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨s, hs, hsr⟩ := Finset.mem_image.mp hr
    obtain ⟨n, hn, hns⟩ := mem_residues.mp hs
    refine mem_residues.mpr ⟨n, hn, ?_⟩
    rw [← hπ n, hns]
    exact hsr
  · intro hr
    obtain ⟨n, hn, hnr⟩ := mem_residues.mp hr
    exact Finset.mem_image.mpr ⟨(n : ZMod (q : ℕ)),
      mem_residues.mpr ⟨n, hn, rfl⟩, (hπ n).trans hnr⟩

theorem card_image_eq_card_image_quotient {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (K : AddSubgroup G) [DecidableEq (G ⧸ K)]
    (π : G →+ H) (hπ : Function.Surjective π) (hker : π.ker = K) (S : Finset G) :
    (S.image π).card = (S.image (QuotientAddGroup.mk' K)).card := by
  classical
  let e : G ⧸ K ≃+ H := (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective π hπ)
  have heq : S.image π = (S.image (QuotientAddGroup.mk' K)).image e := by
    rw [Finset.image_image]
    rfl
  rw [heq, Finset.card_image_of_injective _ e.injective]

theorem card_stabilizer_quotient {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (C S : Finset G) (π : G →+ H) (hπ : Function.Surjective π)
    (hker : π.ker = AddAction.stabilizer G (C : Set G)) :
    C.addStab.card * (S.image π).card = (S + C.addStab).card := by
  classical
  have h := Finset.card_addStab_add_card_image_coe' S C
  have heq := card_image_eq_card_image_quotient (AddAction.stabilizer G (C : Set G)) π hπ hker S
  rw [heq]
  exact h

theorem critical_quotient_card_identity {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (hsmall : (A + B).card < A.card + B.card)
    (π : G →+ H) (hπ : Function.Surjective π)
    (hker : π.ker = AddAction.stabilizer G ((A + B : Finset G) : Set G)) :
    (A.image π).card + (B.image π).card = ((A + B).image π).card + 1 := by
  have hC := hA.add hB
  have hAc := card_stabilizer_quotient (A + B) A π hπ hker
  have hBc := card_stabilizer_quotient (A + B) B π hπ hker
  have hCc := card_stabilizer_quotient (A + B) (A + B) π hπ hker
  rw [Finset.add_addStab] at hCc
  have hk := FiniteKneser.critical_card_identity hA hB hsmall
  have hpos : 0 < (A + B).addStab.card :=
    Finset.card_pos.mpr ⟨0, Finset.zero_mem_addStab.mpr hC⟩
  have heq : (A + B).addStab.card * ((A.image π).card + (B.image π).card) =
      (A + B).addStab.card * (((A + B).image π).card + 1) := by
    rw [Nat.mul_add, hAc, hBc, hk, Nat.mul_add, hCc, Nat.mul_one]
  exact Nat.eq_of_mul_eq_mul_left hpos heq

theorem stabilizer_image_quotient_eq_zero {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (C : Finset G) (hC : C.Nonempty) (π : G →+ H) (hπ : Function.Surjective π)
    (hker : π.ker = AddAction.stabilizer G (C : Set G)) :
    (C.image π).addStab = {0} := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨x, hxt⟩ := hπ t
    have hx : x ∈ C.addStab := by
      apply (Finset.mem_addStab' hC).mpr
      intro c hc
      have htc := (Finset.mem_addStab' (hC.image π)).mp ht
        (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
      obtain ⟨d, hd, hdt⟩ := Finset.mem_image.mp htc
      have hdiff : x + c - d ∈ π.ker := by
        change π (x + c - d) = 0
        rw [map_sub, map_add, hxt, hdt]
        simp
      have hstab : x + c - d ∈ C.addStab := by
        rw [← Finset.mem_coe, Finset.coe_addStab hC]
        change x + c - d ∈ AddAction.stabilizer G (C : Set G)
        rw [← hker]
        exact hdiff
      have hmem := (Finset.mem_addStab' hC).mp hstab hd
      simpa only [vadd_eq_add, sub_add_cancel] using hmem
    have hxker : x ∈ π.ker := by
      rw [hker]
      change x ∈ (AddAction.stabilizer G (C : Set G) : Set G)
      rw [← Finset.coe_addStab hC]
      exact hx
    have hxzero : π x = 0 := hxker
    exact Finset.mem_singleton.mpr (hxt.symm.trans hxzero)
  · intro ht
    have ht0 : t = 0 := Finset.mem_singleton.mp ht
    subst t
    exact Finset.zero_mem_addStab.mpr (hC.image π)

theorem natCard_stabilizer_eq_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (C : Finset G) (hC : C.Nonempty) :
    Nat.card (AddAction.stabilizer G (C : Set G)) = C.addStab.card := by
  classical
  have hset : (AddAction.stabilizer G (C : Set G) : Set G) = (C.addStab : Set G) :=
    (Finset.coe_addStab hC).symm
  calc
    Nat.card (AddAction.stabilizer G (C : Set G)) =
        Nat.card {x : G // x ∈ C.addStab} := Nat.card_congr (Set.equivOfEq hset)
    _ = C.addStab.card := by simp

theorem card_deficit_le_stabilizer {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (hsmall : (A + B).card < A.card + B.card) :
    A.card + B.card ≤ (A + B).card + (A + B).addStab.card := by
  have hzero : (0 : G) ∈ (A + B).addStab := Finset.zero_mem_addStab.mpr (hA.add hB)
  have hAc := Finset.card_le_card (FiniteKneser.subset_add_stabilizer_right A hzero)
  have hBc := Finset.card_le_card (FiniteKneser.subset_add_stabilizer_right B hzero)
  have hidentity := FiniteKneser.critical_card_identity hA hB hsmall
  omega

theorem exists_bounded_critical_cyclic_quotient (q : ℕ+) (A B : Finset (ZMod (q : ℕ)))
    (hA : A.Nonempty) (hB : B.Nonempty) (η : ℝ) (hη : 0 < η)
    (hdef : η * (q : ℕ) ≤ (A.card : ℝ) + B.card - (A + B).card) :
    ∃ (h : ℕ+) (π : ZMod (q : ℕ) →+ ZMod (h : ℕ)),
      (h : ℕ) ∣ (q : ℕ) ∧ Function.Surjective π ∧
      (∀ n : ℕ, π (n : ZMod (q : ℕ)) = (n : ZMod (h : ℕ))) ∧
      (A.image π).card + (B.image π).card = ((A + B).image π).card + 1 ∧
      ((A + B).image π).addStab = {0} ∧ (h : ℕ) ≤ 1 / η := by
  classical
  have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  have hsmallR : ((A + B).card : ℝ) < (A.card : ℝ) + B.card := by nlinarith
  have hsmall : (A + B).card < A.card + B.card := by exact_mod_cast hsmallR
  let C := A + B
  let K := AddAction.stabilizer (ZMod (q : ℕ)) (C : Set (ZMod (q : ℕ)))
  have hC : C.Nonempty := hA.add hB
  obtain ⟨h, π, hindex, hdiv, hπ, hker, hnat⟩ := exists_natural_cyclic_quotient q K
  have hcount := natCard_stabilizer_eq_card C hC
  have hprod : C.addStab.card * (h : ℕ) = (q : ℕ) := by
    rw [hindex, ← hcount]
    simpa only [Nat.card_zmod] using K.card_mul_index
  have hprodR : (C.addStab.card : ℝ) * (h : ℕ) = (q : ℕ) := by exact_mod_cast hprod
  have hdefNat := card_deficit_le_stabilizer A B hA hB hsmall
  have hdefR : (A.card : ℝ) + B.card ≤ (C.card : ℝ) + C.addStab.card := by exact_mod_cast hdefNat
  have hηq : η * (q : ℕ) ≤ (C.addStab.card : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hηq (Nat.cast_nonneg (h : ℕ))
  have hstep : (η * (h : ℕ)) * (q : ℕ) ≤ 1 * (q : ℕ) := by nlinarith
  have hηh : η * (h : ℕ) ≤ 1 := le_of_mul_le_mul_right hstep hq
  have hh : ((h : ℕ) : ℝ) ≤ 1 / η := (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hηh)
  exact ⟨h, π, hdiv, hπ, hnat,
    critical_quotient_card_identity A B hA hB hsmall π hπ hker,
    stabilizer_image_quotient_eq_zero C hC π hπ hker, hh⟩

end Erdos335
