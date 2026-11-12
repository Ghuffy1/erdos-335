import Erdos335.HighGapOrdinaryProfiles
import Erdos335.FiniteSections
import Mathlib.Data.PNat.Prime

/-!
# Ordinary densities at all finite residue moduli in the High branch

Private proof development. Verification status is recorded separately. Densities at lcm(M,m) coarsen to modulus m
by a finite disjoint union. The fixed High modulus bound remains unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Filter Set Topology
open scoped Pointwise BigOperators

noncomputable section

namespace Erdos335

theorem hasDensity_finset_iUnion_of_disjoint
    {I : Type*} (S : Finset I) (T : I → Set ℕ) (d : I → ℝ)
    (hd : ∀ i, HasDensity (T i) (d i))
    (hdisjoint : Pairwise (fun i j => Disjoint (T i) (T j))) :
    HasDensity (⋃ i ∈ S, T i) (∑ i ∈ S, d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hasDensity_empty
  | @insert i S hi ih =>
    have hset : (⋃ j ∈ insert i S, T j) = T i ∪ (⋃ j ∈ S, T j) := by
      ext n
      simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
      aesop
    have hdis : Disjoint (T i) (⋃ j ∈ S, T j) := by
      apply Set.disjoint_left.mpr
      intro n hni hn
      obtain ⟨j, hjn⟩ := Set.mem_iUnion.mp hn
      obtain ⟨hj, hnj⟩ := Set.mem_iUnion.mp hjn
      have hne : i ≠ j := by
        intro hij
        subst j
        exact hi hj
      exact Set.disjoint_left.mp (hdisjoint hne) hni hnj
    rw [hset, Finset.sum_insert hi]
    exact Proposed.hasDensity_union_of_disjoint (hd i) ih hdis

namespace Loeb

theorem literal_residue_density_coarsening
    (A : Set ℕ) (K m : ℕ+) (hmK : (m : ℕ) ∣ (K : ℕ))
    (d : ZMod (K : ℕ) → ℝ)
    (hd : ∀ r, HasDensity {n : ℕ | n ∈ A ∧ (n : ZMod (K : ℕ)) = r} (d r))
    (r : ZMod (m : ℕ)) :
    HasDensity {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
      (∑ s ∈ (Finset.univ.filter (fun s => naturalCyclicProjection K m s = r)), d s) := by
  classical
  let T : ZMod (K : ℕ) → Set ℕ := fun s => {n | n ∈ A ∧ (n : ZMod (K : ℕ)) = s}
  let S : Finset (ZMod (K : ℕ)) :=
    Finset.univ.filter (fun s => naturalCyclicProjection K m s = r)
  have hdisjoint : Pairwise (fun i j => Disjoint (T i) (T j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro n hni hnj
    exact hij (hni.2.symm.trans hnj.2)
  have hset : {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r} = ⋃ s ∈ S, T s := by
    ext n
    constructor
    · rintro ⟨hnA, hnr⟩
      refine Set.mem_iUnion.mpr ⟨(n : ZMod (K : ℕ)), Set.mem_iUnion.mpr ⟨?_, hnA, rfl⟩⟩
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        naturalCyclicProjection_natCast K m hmK n] using hnr
    · intro hn
      obtain ⟨s, hsn⟩ := Set.mem_iUnion.mp hn
      obtain ⟨hs, hns⟩ := Set.mem_iUnion.mp hsn
      refine ⟨hns.1, ?_⟩
      have hproj := (Finset.mem_filter.mp hs).2
      rw [← hns.2, naturalCyclicProjection_natCast K m hmK n] at hproj
      exact hproj
  rw [hset]
  exact hasDensity_finset_iUnion_of_disjoint S T d hd hdisjoint

theorem exists_high_gap_all_residue_densities
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b))
    (hgap : a + b < gamma A B)
    (hhighA : gamma A B < a + b + δA)
    (hhighB : gamma A B < a + b + δB)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (M : ℕ+)
    (hM : ∀ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 →
      (h : ℕ) ∣ (M : ℕ)) :
    ∃ fA fB : NaturalResidueProfile,
      (∀ (m : ℕ+) (r : ZMod (m : ℕ)), HasDensity {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r}
        (fA m r / (m : ℕ))) ∧
      (∀ (m : ℕ+) (r : ZMod (m : ℕ)), HasDensity {n : ℕ | n ∈ B ∧ (n : ZMod (m : ℕ)) = r}
        (fB m r / (m : ℕ))) := by
  classical
  have hper (m : ℕ+) : ∃ u v : ZMod (m : ℕ) → ℝ,
      (∀ r, HasDensity {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r} (u r / (m : ℕ))) ∧
      (∀ r, HasDensity {n : ℕ | n ∈ B ∧ (n : ZMod (m : ℕ)) = r} (v r / (m : ℕ))) := by
    let K : ℕ+ := PNat.lcm M m
    have hMK : (M : ℕ) ∣ (K : ℕ) := by
      simpa only [K, PNat.lcm_coe] using Nat.dvd_lcm_left (M : ℕ) (m : ℕ)
    have hmK : (m : ℕ) ∣ (K : ℕ) := by
      simpa only [K, PNat.lcm_coe] using Nat.dvd_lcm_right (M : ℕ) (m : ℕ)
    have hK : ∀ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 →
        (h : ℕ) ∣ (K : ℕ) := fun h hh => dvd_trans (hM h hh) hMK
    obtain ⟨vA, vB, _, _, _, _, hdA, hdB⟩ := exists_high_gap_ordinary_prefix_profiles
      U hU A B a b δA δB ha hb hAdensity hBdensity hCdensity hgap hhighA hhighB
        hcapA hcapB K hK
    let u : ZMod (m : ℕ) → ℝ := fun r => (m : ℕ) *
      (∑ s ∈ (Finset.univ.filter (fun s => naturalCyclicProjection K m s = r)), vA s / (K : ℕ))
    let v : ZMod (m : ℕ) → ℝ := fun r => (m : ℕ) *
      (∑ s ∈ (Finset.univ.filter (fun s => naturalCyclicProjection K m s = r)), vB s / (K : ℕ))
    have hmne : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
    refine ⟨u, v, ?_, ?_⟩
    · intro r
      simpa only [u, mul_div_cancel_left₀ _ hmne] using
        literal_residue_density_coarsening A K m hmK (fun s => vA s / (K : ℕ)) hdA r
    · intro r
      simpa only [v, mul_div_cancel_left₀ _ hmne] using
        literal_residue_density_coarsening B K m hmK (fun s => vB s / (K : ℕ)) hdB r
  choose fA fB hA hB using hper
  exact ⟨fA, fB, hA, hB⟩

end Loeb

end Erdos335

end
