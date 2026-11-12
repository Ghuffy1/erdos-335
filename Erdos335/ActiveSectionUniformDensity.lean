import Erdos335.ResidueSectionDensity
import Erdos335.NaturalCyclicProjection

/-!
# Uniform densities in a positive-index active section

Private proof development. Verification status is recorded separately.
The refined residue is the actual positive representative of the composed
section map, so the zero residue and the initial offset are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology

namespace Erdos335.Proposed

private theorem positiveRepresentative_le_modulus (q : ℕ+) (r : ZMod (q : ℕ)) :
    positiveRepresentative q r ≤ (q : ℕ) := by
  unfold positiveRepresentative
  split_ifs
  · exact le_rfl
  · exact (ZMod.val_lt r).le

private theorem positiveRepresentative_natCast_of_bounds
    (q : ℕ+) (n : ℕ) (hn : 0 < n) (hnq : n ≤ (q : ℕ)) :
    positiveRepresentative q (n : ZMod (q : ℕ)) = n := by
  by_cases heq : n = (q : ℕ)
  · rw [heq, ZMod.natCast_self]
    simp only [positiveRepresentative, ZMod.val_zero, ite_true]
  · have hlt : n < (q : ℕ) := lt_of_le_of_ne hnq heq
    rw [positiveRepresentative, ZMod.val_natCast_of_lt hlt, if_neg (Nat.ne_of_gt hn)]

def refinedSectionResidue (h m : ℕ+) (i : ZMod (h : ℕ)) (r : ZMod (m : ℕ)) :
    ZMod ((h * m : ℕ+) : ℕ) :=
  (sectionPoint h i (positiveRepresentative m r) : ℕ)

private theorem refinedSectionResidue_representative
    (h m : ℕ+) (i : ZMod (h : ℕ)) (r : ZMod (m : ℕ)) :
    positiveRepresentative (h * m) (refinedSectionResidue h m i r) =
      sectionPoint h i (positiveRepresentative m r) := by
  apply positiveRepresentative_natCast_of_bounds
  · exact sectionPoint_pos h i _
  · have hrep : 0 < positiveRepresentative m r := positiveRepresentative_pos m r
    have hrep_le := positiveRepresentative_le_modulus m r
    have hi_le := positiveRepresentative_le_modulus h i
    change (h : ℕ) * (positiveRepresentative m r - 1) + positiveRepresentative h i ≤
      (h : ℕ) * (m : ℕ)
    calc
      (h : ℕ) * (positiveRepresentative m r - 1) + positiveRepresentative h i ≤
          (h : ℕ) * (positiveRepresentative m r - 1) + h := Nat.add_le_add_left hi_le _
      _ = (h : ℕ) * positiveRepresentative m r := by
        calc
          (h : ℕ) * (positiveRepresentative m r - 1) + h =
              (h : ℕ) * ((positiveRepresentative m r - 1) + 1) := by ring
          _ = (h : ℕ) * positiveRepresentative m r := by rw [Nat.sub_add_cancel hrep]
      _ ≤ (h : ℕ) * (m : ℕ) := Nat.mul_le_mul_left _ hrep_le

theorem refinedSectionResidue_projection
    (h m : ℕ+) (i : ZMod (h : ℕ)) (r : ZMod (m : ℕ)) :
    Loeb.naturalCyclicProjection (h * m) h (refinedSectionResidue h m i r) = i := by
  have hdiv : (h : ℕ) ∣ ((h * m : ℕ+) : ℕ) := ⟨m, rfl⟩
  rw [refinedSectionResidue, Loeb.naturalCyclicProjection_natCast (h * m) h hdiv]
  exact sectionPoint_cast h i (positiveRepresentative m r)

private theorem sectionPoint_compose
    (h m : ℕ+) (i : ZMod (h : ℕ)) (r : ZMod (m : ℕ)) (k : ℕ) :
    sectionPoint h i (sectionPoint m r k) =
      sectionPoint (h * m) (refinedSectionResidue h m i r) k := by
  change (h : ℕ) * ((m : ℕ) * (k - 1) + positiveRepresentative m r - 1) +
      positiveRepresentative h i =
    ((h * m : ℕ+) : ℕ) * (k - 1) +
      positiveRepresentative (h * m) (refinedSectionResidue h m i r)
  rw [refinedSectionResidue_representative,
    Nat.add_sub_assoc (positiveRepresentative_pos m r)]
  change (h : ℕ) * ((m : ℕ) * (k - 1) + (positiveRepresentative m r - 1)) +
      positiveRepresentative h i =
    ((h : ℕ) * (m : ℕ)) * (k - 1) +
      ((h : ℕ) * (positiveRepresentative m r - 1) + positiveRepresentative h i)
  ring

theorem residueSection_compose
    (A : Set ℕ) (h m : ℕ+) (i : ZMod (h : ℕ)) (r : ZMod (m : ℕ)) :
    residueSection (residueSection A h i) m r =
      residueSection A (h * m) (refinedSectionResidue h m i r) := by
  ext k
  change (0 < k ∧ 0 < sectionPoint m r k ∧ sectionPoint h i (sectionPoint m r k) ∈ A) ↔
    (0 < k ∧ sectionPoint (h * m) (refinedSectionResidue h m i r) k ∈ A)
  rw [sectionPoint_compose]
  constructor
  · exact fun hk => ⟨hk.1, hk.2.2⟩
  · exact fun hk => ⟨hk.1, sectionPoint_pos m r k, hk.2⟩

theorem residueSection_uniform_residue_density
    (A : Set ℕ) (h : ℕ+) (i : ZMod (h : ℕ)) (x : ℝ)
    (hA : A ⊆ Set.Ioi 0)
    (hdens : ∀ m : ℕ+, ∀ r : ZMod ((h * m : ℕ+) : ℕ),
      Loeb.naturalCyclicProjection (h * m) h r = i →
        HasDensity (residueFiber A r) (x / ((h * m : ℕ+) : ℕ))) :
    ∀ m : ℕ+, ∀ r : ZMod (m : ℕ),
      HasDensity (residueFiber (residueSection A h i) r) (x / (m : ℕ)) := by
  intro m r
  have hF := hdens m (refinedSectionResidue h m i r) (refinedSectionResidue_projection h m i r)
  have hsection := hasDensity_residueSection_of_fiber A (h * m)
    (refinedSectionResidue h m i r) (x / ((h * m : ℕ+) : ℕ)) hA hF
  have hden : (((h * m : ℕ+) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (h * m).ne_zero
  have hcancel : (((h * m : ℕ+) : ℕ) : ℝ) * (x / ((h * m : ℕ+) : ℕ)) = x := by
    field_simp
  rw [hcancel, ← residueSection_compose A h m i r] at hsection
  exact hasDensity_residueFiber (fun _ hk => hk.1) hsection

end Erdos335.Proposed
