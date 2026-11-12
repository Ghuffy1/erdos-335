import Erdos335.PartialResidueProfileAlignment
import Erdos335.FinitePartialMass
import Erdos335.Residues

/-!
# Finite profiles for paired positive local terminals

Private proof development. Verification status is recorded separately. The record permits singleton supports and
therefore also represents whole Bohr pairs with empty backgrounds.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

abbrev NaturalResidueProfile := (m : ℕ+) → ZMod (m : ℕ) → ℝ

noncomputable def positiveResiduePattern (h : ℕ+)
    (S : Finset (ZMod (h : ℕ))) (i : ZMod (h : ℕ)) (x : ℝ)
    (m : ℕ+) (r : ZMod (m : ℕ)) : ℝ := by
  classical
  exact if naturalCyclicProjection m h r = i then x
    else if naturalCyclicProjection m h r ∈ S then 1 else 0

structure LocalPositiveResidueProfile
    (h : ℕ+) (A B : Set ℕ) (a b : ℝ)
    (moving prefixProfile output : NaturalResidueProfile) where
  movingSupport : Finset (ZMod (h : ℕ))
  support_subset : movingSupport ⊆ residues (h : ℕ) A
  activeMoving : ZMod (h : ℕ)
  activePrefix : ZMod (h : ℕ)
  activeMoving_mem : activeMoving ∈ movingSupport
  activePrefix_mem : activePrefix ∈ residues (h : ℕ) B
  movingMass : ℝ
  prefixMass : ℝ
  moving_positive : 0 < movingMass
  prefix_positive : 0 < prefixMass
  mass_sum_lt_one : movingMass + prefixMass < 1
  total_moving : (h : ℕ) * a = (movingSupport.card : ℝ) - 1 + movingMass
  total_prefix : (h : ℕ) * b = ((residues (h : ℕ) B).card : ℝ) - 1 + prefixMass
  cardinality : (movingSupport + residues (h : ℕ) B).card + 1 =
    movingSupport.card + (residues (h : ℕ) B).card
  unique_expression : ∀ r ∈ movingSupport, ∀ s ∈ residues (h : ℕ) B,
    r + s = activeMoving + activePrefix → r = activeMoving ∧ s = activePrefix
  moving_profile : ∀ m : ℕ+, (h : ℕ) ∣ (m : ℕ) → ∀ r : ZMod (m : ℕ),
    moving m r = positiveResiduePattern h movingSupport activeMoving movingMass m r
  prefix_profile : ∀ m : ℕ+, (h : ℕ) ∣ (m : ℕ) → ∀ r : ZMod (m : ℕ),
    prefixProfile m r = positiveResiduePattern h (residues (h : ℕ) B) activePrefix prefixMass m r
  output_profile : ∀ m : ℕ+, (h : ℕ) ∣ (m : ℕ) → ∀ r : ZMod (m : ℕ),
    output m r = positiveResiduePattern h (movingSupport + residues (h : ℕ) B)
      (activeMoving + activePrefix) (movingMass + prefixMass) m r

theorem paired_positive_profiles_match
    (h k : ℕ+) (A B : Set ℕ) (a b : ℝ)
    (movingA movingB prefixA prefixB output : NaturalResidueProfile)
    (p : LocalPositiveResidueProfile h A B a b movingA prefixB output)
    (q : LocalPositiveResidueProfile k B A b a movingB prefixA output) :
    h = k ∧ p.movingSupport = residues (h : ℕ) A ∧
      q.movingSupport = residues (k : ℕ) B ∧
      p.movingMass = q.prefixMass ∧ p.prefixMass = q.movingMass ∧
      ∀ m : ℕ+, (h : ℕ) ∣ (m : ℕ) →
        (∀ r : ZMod (m : ℕ), movingA m r = prefixA m r) ∧
        (∀ r : ZMod (m : ℕ), movingB m r = prefixB m r) := by
  classical
  let N : ℕ+ := h * k
  have hhN : (h : ℕ) ∣ (N : ℕ) := ⟨k, rfl⟩
  have hkN : (k : ℕ) ∣ (N : ℕ) := ⟨h, Nat.mul_comm _ _⟩
  have hp (r : ZMod (N : ℕ)) : output N r =
      if naturalCyclicProjection N h r = p.activeMoving + p.activePrefix
        then p.movingMass + p.prefixMass
      else if naturalCyclicProjection N h r ∈ p.movingSupport + residues (h : ℕ) B
        then 1 else 0 := p.output_profile N hhN r
  have hq (r : ZMod (N : ℕ)) : output N r =
      if naturalCyclicProjection N k r = q.activeMoving + q.activePrefix
        then q.movingMass + q.prefixMass
      else if naturalCyclicProjection N k r ∈ q.movingSupport + residues (k : ℕ) A
        then 1 else 0 := q.output_profile N hkN r
  obtain ⟨hhk, _, hpartial⟩ := partial_residue_profile_alignment N h k hhN hkN
    (p.activeMoving + p.activePrefix) (q.activeMoving + q.activePrefix)
    (p.movingSupport + residues (h : ℕ) B) (q.movingSupport + residues (k : ℕ) A)
    (p.movingMass + p.prefixMass) (q.movingMass + q.prefixMass)
    (add_pos p.moving_positive p.prefix_positive) p.mass_sum_lt_one
    (add_pos q.moving_positive q.prefix_positive) q.mass_sum_lt_one (output N) hp hq
  subst k
  have hpmoving_lt : p.movingMass < 1 := by linarith [p.mass_sum_lt_one, p.prefix_positive]
  have hpprefix_lt : p.prefixMass < 1 := by linarith [p.mass_sum_lt_one, p.moving_positive]
  have hqmoving_lt : q.movingMass < 1 := by linarith [q.mass_sum_lt_one, q.prefix_positive]
  have hqprefix_lt : q.prefixMass < 1 := by linarith [q.mass_sum_lt_one, q.moving_positive]
  have hmassA : (p.movingSupport.card : ℝ) - 1 + p.movingMass =
      ((residues (h : ℕ) A).card : ℝ) - 1 + q.prefixMass :=
    p.total_moving.symm.trans q.total_prefix
  have hmassB : (q.movingSupport.card : ℝ) - 1 + q.movingMass =
      ((residues (h : ℕ) B).card : ℝ) - 1 + p.prefixMass :=
    q.total_moving.symm.trans p.total_prefix
  obtain ⟨hSA, hx⟩ := FiniteProfiles.support_eq_of_partial_mass p.movingSupport
    (residues (h : ℕ) A) p.support_subset p.movingMass q.prefixMass
    p.moving_positive hpmoving_lt q.prefix_positive hqprefix_lt hmassA
  obtain ⟨hSB, hy⟩ := FiniteProfiles.support_eq_of_partial_mass q.movingSupport
    (residues (h : ℕ) B) q.support_subset q.movingMass p.prefixMass
    q.moving_positive hqmoving_lt p.prefix_positive hpprefix_lt hmassB
  obtain ⟨r, hr⟩ := naturalCyclicProjection_surjective N h hhN
    (p.activeMoving + p.activePrefix)
  have hactiveSum : p.activeMoving + p.activePrefix = q.activeMoving + q.activePrefix :=
    hr.symm.trans ((hpartial r).mp hr)
  have hqa : q.activePrefix ∈ p.movingSupport := by
    rw [hSA]
    exact q.activePrefix_mem
  have hqb : q.activeMoving ∈ residues (h : ℕ) B := by
    rw [← hSB]
    exact q.activeMoving_mem
  obtain ⟨hi, hj⟩ := p.unique_expression q.activePrefix hqa q.activeMoving hqb
    ((add_comm _ _).trans hactiveSum.symm)
  refine ⟨rfl, hSA, hSB, hx, hy.symm, ?_⟩
  intro m hm
  constructor
  · intro r
    rw [p.moving_profile m hm r, q.prefix_profile m hm r, hSA, ← hi, hx]
  · intro r
    rw [q.moving_profile m hm r, p.prefix_profile m hm r, hSB, hj, hy]

end Erdos335.Loeb

end
