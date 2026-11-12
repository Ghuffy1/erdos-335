import Erdos335.PositivePairProfiles

/-!
# Finite scalar values of positive local residue profiles

Private proof development. Verification status is recorded separately. The finite sets depend only on the density
and the bound for the local modulus. They overapproximate the possible
coordinate values without enumerating supports or dependent profile records.
-/

set_option autoImplicit false

open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

def positiveProfileScalarValues (D : ℕ) (c : ℝ) : Finset ℝ := by
  classical
  exact {0, 1} ∪ (Finset.Icc 1 D).biUnion (fun h : ℕ =>
    (Finset.Icc 0 h).image (fun j : ℕ => (h : ℝ) * c - (j : ℝ) + 1))

theorem positiveResiduePattern_mem_scalarValues
    (h : ℕ+) (D : ℕ) (hD : (h : ℕ) ≤ D)
    (S : Finset (ZMod (h : ℕ))) (i : ZMod (h : ℕ)) (x c : ℝ)
    (hmass : (h : ℕ) * c = (S.card : ℝ) - 1 + x)
    (m : ℕ+) (r : ZMod (m : ℕ)) :
    positiveResiduePattern h S i x m r ∈ positiveProfileScalarValues D c := by
  classical
  have hcard : S.card ≤ (h : ℕ) := by
    simpa only [ZMod.card] using Finset.card_le_univ S
  have hx : x ∈ positiveProfileScalarValues D c := by
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨(h : ℕ), Finset.mem_Icc.mpr ⟨h.pos, hD⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨S.card, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hcard⟩, ?_⟩
    linarith
  unfold positiveResiduePattern
  split_ifs
  · exact hx
  · exact Finset.mem_union.mpr (Or.inl (by simp))
  · exact Finset.mem_union.mpr (Or.inl (by simp))

theorem LocalPositiveResidueProfile.total_output
    {h : ℕ+} {A B : Set ℕ} {a b : ℝ}
    {moving prefixProfile output : NaturalResidueProfile}
    (p : LocalPositiveResidueProfile h A B a b moving prefixProfile output) :
    (h : ℕ) * (a + b) =
      ((p.movingSupport + residues (h : ℕ) B).card : ℝ) - 1 +
        (p.movingMass + p.prefixMass) := by
  have hcard : ((p.movingSupport + residues (h : ℕ) B).card : ℝ) + 1 =
      (p.movingSupport.card : ℝ) + (residues (h : ℕ) B).card := by
    exact_mod_cast p.cardinality
  calc
    (h : ℕ) * (a + b) = (h : ℕ) * a + (h : ℕ) * b := mul_add _ _ _
    _ = ((p.movingSupport + residues (h : ℕ) B).card : ℝ) - 1 +
        (p.movingMass + p.prefixMass) := by
      rw [p.total_moving, p.total_prefix]
      linarith

theorem LocalPositiveResidueProfile.scalar_values
    {h : ℕ+} {A B : Set ℕ} {a b : ℝ}
    {moving prefixProfile output : NaturalResidueProfile}
    (p : LocalPositiveResidueProfile h A B a b moving prefixProfile output)
    (D : ℕ) (hD : (h : ℕ) ≤ D)
    (m : ℕ+) (hm : (h : ℕ) ∣ (m : ℕ)) (r : ZMod (m : ℕ)) :
    moving m r ∈ positiveProfileScalarValues D a ∧
      prefixProfile m r ∈ positiveProfileScalarValues D b ∧
        output m r ∈ positiveProfileScalarValues D (a + b) := by
  constructor
  · rw [p.moving_profile m hm r]
    exact positiveResiduePattern_mem_scalarValues h D hD p.movingSupport
      p.activeMoving p.movingMass a p.total_moving m r
  constructor
  · rw [p.prefix_profile m hm r]
    exact positiveResiduePattern_mem_scalarValues h D hD (residues (h : ℕ) B)
      p.activePrefix p.prefixMass b p.total_prefix m r
  · rw [p.output_profile m hm r]
    exact positiveResiduePattern_mem_scalarValues h D hD
      (p.movingSupport + residues (h : ℕ) B) (p.activeMoving + p.activePrefix)
      (p.movingMass + p.prefixMass) (a + b) p.total_output m r

end Erdos335.Loeb

end
