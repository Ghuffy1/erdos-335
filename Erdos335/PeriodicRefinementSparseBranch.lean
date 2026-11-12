import Erdos335.PeriodicRefinementSparsePacking
import Erdos335.FiniteFrameDensityNecessity
import Erdos335.PeriodicSummandFrame
import Erdos335.PeriodicBackgroundParts

/-!
# The exact sparse-section alternative in the periodic refinement

Private proof development. Verification status is recorded separately.
The finite and infinite terminals retain the literal normalized sparse set.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Proposed

def SparseTerminalCondition (U V : Set ℕ) : Prop :=
  ∃ u₀ : ℕ, IsLeast U u₀ ∧
    (U = {u₀} ∨ ∃ g : ℕ+,
      (g : ℕ) = Nat.setGcd (tailShift U u₀) ∧
      DensityEquivalent (shift V (g : ℕ)) V ∧
      (U.Finite ∨ (U.Infinite ∧ SparseResiduePacking (tailShift U u₀) V g)))

theorem sparse_terminal_of_sum_density (U V : Set ℕ) (x : ℝ)
    (hU : U.Nonempty) (hV : HasDensity V x) (hsum : HasDensity (U + V) x) :
    SparseTerminalCondition U V := by
  classical
  obtain ⟨u₀, hu₀⟩ := sparse_minimum_exists U hU
  refine ⟨u₀, hu₀, ?_⟩
  by_cases hsingle : U = {u₀}
  · exact Or.inl hsingle
  right
  let g : ℕ+ := ⟨Nat.setGcd (tailShift U u₀), sparse_normalized_setGcd_pos U u₀ hu₀ hsingle⟩
  have hzero := sparse_normalized_zero U u₀ hu₀
  have hnormalized : HasDensity (tailShift U u₀ + V) x :=
    (sparse_normalized_density_iff U V u₀ x hu₀).mpr hsum
  have hperiod : DensityEquivalent (shift V (g : ℕ)) V := by
    change DensityEquivalent (shift V (Nat.setGcd (tailShift U u₀))) V
    exact sparse_sum_setGcd_period (tailShift U u₀) V x hzero hV hnormalized
  refine ⟨g, rfl, hperiod, ?_⟩
  by_cases hfinite : U.Finite
  · exact Or.inl hfinite
  right
  refine ⟨hfinite, ?_⟩
  have hdiv : ∀ d ∈ tailShift U u₀, (g : ℕ) ∣ d := by
    intro d hd
    change Nat.setGcd (tailShift U u₀) ∣ d
    exact Nat.setGcd_dvd_of_mem hd
  apply (sparse_residue_packing_iff (tailShift U u₀) V g hdiv).mpr
  exact (sparse_sum_density_iff_negligible (tailShift U u₀) V x hzero hV).mp hnormalized

theorem SparseTerminalCondition.hasDensity {U V : Set ℕ} {x : ℝ}
    (h : SparseTerminalCondition U V) (hV : HasDensity V x) :
    HasDensity (U + V) x := by
  obtain ⟨u₀, hu₀, hsingle | ⟨g, hg, hperiod, hfinite | ⟨_, hpacking⟩⟩⟩ := h
  · rw [hsingle, singleton_add_eq_shift]
    exact hV.shift u₀
  · have hperiod' : DensityEquivalent (shift V (Nat.setGcd (tailShift U u₀))) V := by
      rw [← hg]
      exact hperiod
    have hnormalized := sparse_finite_sum_density_of_setGcd_period (tailShift U u₀) V x
      (sparse_normalized_finite U u₀ hu₀ hfinite) (sparse_normalized_zero U u₀ hu₀) hV hperiod'
    exact (sparse_normalized_density_iff U V u₀ x hu₀).mp hnormalized
  · have hdiv : ∀ d ∈ tailShift U u₀, (g : ℕ) ∣ d := by
      intro d hd
      rw [hg]
      exact Nat.setGcd_dvd_of_mem hd
    have hmissing := (sparse_residue_packing_iff (tailShift U u₀) V g hdiv).mp hpacking
    have hnormalized := (sparse_sum_density_iff_negligible (tailShift U u₀) V x
      (sparse_normalized_zero U u₀ hu₀) hV).mpr hmissing
    exact (sparse_normalized_density_iff U V u₀ x hu₀).mp hnormalized

theorem sparse_terminal_iff_sum_density (U V : Set ℕ) (x : ℝ)
    (hU : U.Nonempty) (hV : HasDensity V x) :
    SparseTerminalCondition U V ↔ HasDensity (U + V) x :=
  ⟨fun h => h.hasDensity hV, sparse_terminal_of_sum_density U V x hU hV⟩

def SparseSectionBranch (A B : Set ℕ) : Prop :=
  ∃ f : FiniteFrame A B, ∃ x : ℝ, 0 < x ∧ x < 1 ∧
    ((HasDensity (residueSection A f.modulus f.activeA) 0 ∧
      HasDensity (residueSection B f.modulus f.activeB) x ∧
      SparseTerminalCondition (residueSection A f.modulus f.activeA)
        (residueSection B f.modulus f.activeB)) ∨
     (HasDensity (residueSection B f.modulus f.activeB) 0 ∧
      HasDensity (residueSection A f.modulus f.activeA) x ∧
      SparseTerminalCondition (residueSection B f.modulus f.activeB)
        (residueSection A f.modulus f.activeA)))

theorem sparse_section_nonempty (A : Set ℕ) (hA : A ⊆ Ioi 0)
    (q : ℕ+) (r : ZMod (q : ℕ)) (hr : r ∈ residues (q : ℕ) A) :
    (residueSection A q r).Nonempty := by
  obtain ⟨a, ha, har⟩ := mem_residues.mp hr
  have hf : a ∈ residueFiber A r :=
    ⟨ha, hA ha, by simpa only [Finset.mem_singleton] using har⟩
  rw [residueFiber_eq_image] at hf
  obtain ⟨k, hk, _⟩ := hf
  exact ⟨k, hk⟩

theorem SparseSectionBranch.swap {A B : Set ℕ} (h : SparseSectionBranch A B) :
    SparseSectionBranch B A := by
  obtain ⟨f, x, hxpos, hxlt, hcase⟩ := h
  exact ⟨f.swap, x, hxpos, hxlt, hcase.symm⟩

theorem FiniteFrame.null_left_periodic_input
    {A B : Set ℕ} (f : FiniteFrame A B) (hApos : A ⊆ Ioi 0)
    (hzero : HasDensity (residueSection A f.modulus f.activeA) 0) :
    DensityEquivalent A
      (periodicSet ((residues (f.modulus : ℕ) A).erase f.activeA)) := by
  have hz : Negligible (residueFiber A f.activeA) := by
    change HasDensity (residueFiber A f.activeA) 0
    simpa only [zero_div] using hasDensity_residueFiber hApos hzero
  have heq := equivalent_periodic_background_and_fiber A f.modulus f.activeA hApos
    (fun r hr hri => missing_fiber_of_full_section hApos (f.backgroundA r hr hri))
  have hempty : DensityEquivalent (residueFiber A f.activeA) (∅ : Set ℕ) := by
    constructor
    · simpa using hz
    · simpa only [Set.empty_diff] using
        (show Negligible (∅ : Set ℕ) from hasDensity_empty)
  have hremove := (DensityEquivalent.refl
    (periodicSet ((residues (f.modulus : ℕ) A).erase f.activeA))).union hempty
  exact heq.trans (by simpa only [Set.union_empty] using hremove)

theorem SparseSectionBranch.periodic_input {A B : Set ℕ}
    (h : SparseSectionBranch A B) (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0) :
    ∃ (m : ℕ+) (P : Finset (ZMod (m : ℕ))),
      DensityEquivalent A (periodicSet P) ∨ DensityEquivalent B (periodicSet P) := by
  obtain ⟨f, _, _, _, hleft | hright⟩ := h
  · exact ⟨f.modulus, (residues (f.modulus : ℕ) A).erase f.activeA,
      Or.inl (f.null_left_periodic_input hApos hleft.1)⟩
  · exact ⟨f.modulus, (residues (f.modulus : ℕ) B).erase f.activeB,
      Or.inr (f.swap.null_left_periodic_input hBpos hright.1)⟩

theorem FiniteFrame.null_left_sum_iff_sparse_terminal
    {A B : Set ℕ} (f : FiniteFrame A B)
    (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (a b x : ℝ) (hA : HasDensity A a) (hB : HasDensity B b)
    (hzero : HasDensity (residueSection A f.modulus f.activeA) 0)
    (hactive : HasDensity (residueSection B f.modulus f.activeB) x) :
    HasDensity (A + B) (a + b) ↔
      SparseTerminalCondition (residueSection A f.modulus f.activeA)
        (residueSection B f.modulus f.activeB) := by
  have hsum := f.sum_density_iff_active_sections hApos hBpos a b 0 x hA hB hzero hactive
  have hterminal := sparse_terminal_iff_sum_density
    (residueSection A f.modulus f.activeA) (residueSection B f.modulus f.activeB) x
    (sparse_section_nonempty A hApos f.modulus f.activeA f.activeA_mem) hactive
  simp only [zero_add] at hsum
  exact hsum.trans hterminal.symm

theorem SparseSectionBranch.hasDensity {A B : Set ℕ} {a b : ℝ}
    (h : SparseSectionBranch A B) (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (hA : HasDensity A a) (hB : HasDensity B b) : HasDensity (A + B) (a + b) := by
  obtain ⟨f, x, _, _, hleft | hright⟩ := h
  · exact (f.null_left_sum_iff_sparse_terminal hApos hBpos a b x hA hB
      hleft.1 hleft.2.1).mpr hleft.2.2
  · have hs := (f.swap.null_left_sum_iff_sparse_terminal hBpos hApos b a x hB hA
      hright.1 hright.2.1).mpr hright.2.2
    simpa only [add_comm B A, add_comm b a] using hs

theorem FiniteFrame.null_left_sparse_branch
    {A B : Set ℕ} (f : FiniteFrame A B)
    (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (a b x : ℝ) (hA : HasDensity A a) (hB : HasDensity B b)
    (hC : HasDensity (A + B) (a + b))
    (hzero : HasDensity (residueSection A f.modulus f.activeA) 0)
    (hactive : HasDensity (residueSection B f.modulus f.activeB) x)
    (hxpos : 0 < x) (hxlt : x < 1) : SparseSectionBranch A B := by
  refine ⟨f, x, hxpos, hxlt, Or.inl ⟨hzero, hactive, ?_⟩⟩
  exact (f.null_left_sum_iff_sparse_terminal hApos hBpos a b x hA hB hzero hactive).mp hC

theorem sparse_branch_of_strict_periodic_summand
    (A B : Set ℕ) (a b : ℝ) (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hA : HasDensity A a) (hB : HasDensity B b)
    (hC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (m : ℕ+) (P : Finset (ZMod (m : ℕ)))
    (hAP : DensityEquivalent A (periodicSet P))
    (hstrict : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) < a + b) :
    SparseSectionBranch A B := by
  obtain ⟨f, x, _, hzero, hactive, hxpos, hxlt⟩ := periodic_summand_strict_finite_frame
    A B a b hApos hBpos ha hb hA hB hC hgap m P hAP hstrict
  exact f.null_left_sparse_branch hApos hBpos a b x hA hB hC hzero hactive hxpos hxlt

end Erdos335.Proposed

end
