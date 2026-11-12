import Erdos335.Residues

/-!
# Finite literal difference representatives at bounded residue moduli
-/

set_option autoImplicit false

open Set

namespace Erdos335

theorem finite_family_difference_representatives
    {I : Type*} [Fintype I] (E : I → Set ℕ) :
    ∃ D : Finset ℕ, (∀ t ∈ D, 0 < t) ∧
      ∀ i, (∃ x ∈ E i, ∃ y ∈ E i, x < y) →
        ∃ x ∈ E i, ∃ y ∈ E i, x < y ∧ y - x ∈ D := by
  classical
  let J := {i : I // ∃ x ∈ E i, ∃ y ∈ E i, x < y}
  haveI : Fintype J := Fintype.ofFinite J
  choose x hx y hy hxy using (fun i : J => i.property)
  let D := Finset.univ.image (fun i : J => y i - x i)
  refine ⟨D, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact Nat.sub_pos_of_lt (hxy i)
  · intro i hi
    let j : J := ⟨i, hi⟩
    exact ⟨x j, hx j, y j, hy j, hxy j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

theorem finite_residue_difference_representatives (B : Set ℕ) (N : ℕ) :
    ∃ D : Finset ℕ, (∀ t ∈ D, 0 < t) ∧
      ∀ (h : ℕ+) (r : ZMod (h : ℕ)), (h : ℕ) ≤ N →
        (∃ x ∈ B, ∃ y ∈ B, x < y ∧ (x : ZMod (h : ℕ)) = r ∧ (y : ZMod (h : ℕ)) = r) →
        ∃ x ∈ B, ∃ y ∈ B, x < y ∧ (x : ZMod (h : ℕ)) = r ∧
          (y : ZMod (h : ℕ)) = r ∧ y - x ∈ D := by
  classical
  let I := ↥(Finset.Icc 1 N)
  letI (h : I) : NeZero (h : ℕ) := ⟨by
    have hh := (Finset.mem_Icc.mp h.property).1
    omega⟩
  let E (i : Σ h : I, ZMod (h : ℕ)) : Set ℕ := {n | n ∈ B ∧ (n : ZMod (i.1 : ℕ)) = i.2}
  obtain ⟨D, hD, hchoice⟩ := finite_family_difference_representatives E
  refine ⟨D, hD, ?_⟩
  intro h r hh hex
  let k : I := ⟨(h : ℕ), Finset.mem_Icc.mpr ⟨h.pos, hh⟩⟩
  have hpair : ∃ x ∈ E ⟨k, r⟩, ∃ y ∈ E ⟨k, r⟩, x < y := by
    obtain ⟨x, hx, y, hy, hxy, hxr, hyr⟩ := hex
    exact ⟨x, ⟨hx, hxr⟩, y, ⟨hy, hyr⟩, hxy⟩
  obtain ⟨x, hx, y, hy, hxy, hdiff⟩ := hchoice ⟨k, r⟩ hpair
  exact ⟨x, hx.1, y, hy.1, hxy, hx.2, hy.2, hdiff⟩

end Erdos335
