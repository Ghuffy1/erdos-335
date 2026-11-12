import Erdos335.DensityAlgebra
import Erdos335.FiniteKneser

/-!
# Exact density criterion for two periodic cores

The inputs may contain arbitrary density-zero fringes. Their literal residues
are retained in the baseline and the escaping sumset.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem negligible_periodic_diff_of_singletons {q : ℕ} [NeZero q]
    (U : Finset (ZMod q)) (C : Set ℕ)
    (h : ∀ r ∈ U, Negligible (periodicSet ({r} : Finset (ZMod q)) \ C)) :
    Negligible (periodicSet U \ C) := by
  have hUnion := negligible_finiteUnion U
    (fun r => periodicSet ({r} : Finset (ZMod q)) \ C) h
  apply hUnion.mono
  rintro n ⟨hnU, hnC⟩
  exact ⟨(n : ZMod q), hnU.2, ⟨⟨hnU.1, by simp⟩, hnC⟩⟩

theorem missing_left_baseline_singleton {q : ℕ} [NeZero q]
    {A B : Set ℕ} {T : Finset (ZMod q)}
    (hB : DensityEquivalent B (periodicSet T))
    {w : ZMod q} (hw : w ∈ residues q A + T) :
    Negligible (periodicSet ({w} : Finset (ZMod q)) \ (A + B)) := by
  classical
  obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hw
  obtain ⟨a, ha, rfl⟩ := mem_residues.mp hr
  have heq := (DensityEquivalent.shift hB a).trans (shift_periodic_equiv T a)
  have hsub : periodicSet ({(a : ZMod q) + t} : Finset (ZMod q)) ⊆
      periodicSet ({(a : ZMod q)} + T) := by
    apply periodicSet_mono
    intro z hz
    have hz' : z = (a : ZMod q) + t := by simpa using hz
    subst z
    exact Finset.add_mem_add (by simp) ht
  apply heq.2.mono
  rintro n ⟨hnP, hnC⟩
  exact ⟨hsub hnP, fun hnShift => hnC (shift_subset_sum ha hnShift)⟩

theorem periodic_baseline_missing_negligible {q : ℕ} [NeZero q]
    {A B : Set ℕ} {S T : Finset (ZMod q)}
    (hA : DensityEquivalent A (periodicSet S))
    (hB : DensityEquivalent B (periodicSet T)) :
    Negligible (periodicSet (baseline A B S T) \ (A + B)) := by
  apply negligible_periodic_diff_of_singletons
  intro w hw
  change w ∈ (residues q A + T) ∪ (S + residues q B) at hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact missing_left_baseline_singleton hB hw
  · have hw' : w ∈ residues q B + S := by simpa only [add_comm] using hw
    have h := missing_left_baseline_singleton (A := B) (B := A) hA hw'
    simpa only [add_comm] using h

theorem sumset_positive {A B : Set ℕ}
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) : A + B ⊆ Set.Ioi 0 := by
  rintro n ⟨a, ha, b, hb, rfl⟩
  have ha0 : 0 < a := hA ha
  have hb0 : 0 < b := hB hb
  change 0 < a + b
  omega

/-- Exact criterion with the escaping set expressed directly as an output difference. -/
theorem periodic_inputs_criterion {q : ℕ} [NeZero q]
    (A B : Set ℕ) (S T : Finset (ZMod q))
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hA : DensityEquivalent A (periodicSet S))
    (hB : DensityEquivalent B (periodicSet T)) :
    HasDensity (A + B) ((S.card : ℝ) / q + (T.card : ℝ) / q) ↔
      (baseline A B S T).card = S.card + T.card ∧
        Negligible ((A + B) \ periodicSet (baseline A B S T)) := by
  classical
  let U := baseline A B S T
  change HasDensity (A + B) ((S.card : ℝ) / q + (T.card : ℝ) / q) ↔
    U.card = S.card + T.card ∧ Negligible ((A + B) \ periodicSet U)
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hP : HasDensity (periodicSet U) ((U.card : ℝ) / q) := hasDensity_periodicSet U
  have hhole : Negligible (periodicSet U \ (A + B)) :=
    periodic_baseline_missing_negligible hA hB
  have hSRA : S ⊆ residues q A := periodic_core_subset_residues hA
  have hcore : S + T ⊆ U :=
    (Finset.add_subset_add hSRA (Finset.Subset.refl T)).trans Finset.subset_union_left
  constructor
  · intro hC
    have hD := hC.sdiff_of_negligible_reverse hP hhole
    have hNonneg := hD.nonneg
    have hdiv : (U.card : ℝ) / q ≤ ((S.card : ℝ) + T.card) / q := by
      rw [add_div]
      linarith
    have hreal : (U.card : ℝ) ≤ (S.card : ℝ) + T.card := by
      have hmul := (div_le_div_iff₀ hq hq).mp hdiv
      nlinarith
    have hle : U.card ≤ S.card + T.card := by exact_mod_cast hreal
    have hnotSmall : ¬U.card < S.card + T.card := by
      intro hsmall
      have hsup : residues q A + residues q B ⊆ S + T :=
        FiniteKneser.extended_support_sum_subset hS hT hcore
          Finset.subset_union_left Finset.subset_union_right hsmall
      have hres : residues q (A + B) ⊆ U := by
        rw [residues_add]
        exact hsup.trans hcore
      have hCsub : A + B ⊆ periodicSet U :=
        (subset_periodic_residues q (A + B) (sumset_positive hApos hBpos)).trans
          (periodicSet_mono hres)
      have hDzero : Negligible ((A + B) \ periodicSet U) := by
        apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
        rintro n ⟨hn, hnP⟩
        exact (hnP (hCsub hn)).elim
      have hEq : DensityEquivalent (A + B) (periodicSet U) := ⟨hDzero, hhole⟩
      have hSame := hC.unique (hEq.symm.hasDensity hP)
      rw [← add_div] at hSame
      have hcounts : (S.card : ℝ) + T.card = U.card :=
        (div_left_inj' (ne_of_gt hq)).mp hSame
      have hcountsNat : S.card + T.card = U.card := by exact_mod_cast hcounts
      omega
    have hcard : U.card = S.card + T.card := by omega
    refine ⟨hcard, ?_⟩
    change HasDensity ((A + B) \ periodicSet U) 0
    simpa only [hcard, Nat.cast_add, add_div, sub_self] using hD
  · rintro ⟨hcard, hD⟩
    have hEq : DensityEquivalent (A + B) (periodicSet U) := ⟨hD, hhole⟩
    have hC := hEq.symm.hasDensity hP
    simpa only [hcard, Nat.cast_add, add_div] using hC

/-- The literal sparse-fringe form of the same complete periodic-core criterion. -/
theorem periodic_inputs_fringe_criterion {q : ℕ} [NeZero q]
    (A B : Set ℕ) (S T : Finset (ZMod q))
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hA : DensityEquivalent A (periodicSet S))
    (hB : DensityEquivalent B (periodicSet T)) :
    HasDensity (A + B) ((S.card : ℝ) / q + (T.card : ℝ) / q) ↔
      (baseline A B S T).card = S.card + T.card ∧
        Negligible (((A \ periodicSet S) + (B \ periodicSet T)) \
          periodicSet (baseline A B S T)) := by
  have h := periodic_inputs_criterion A B S T hApos hBpos hS hT hA hB
  rwa [escaping_sum_eq q A B hApos hBpos S T] at h

/-- The periodic-core criterion stated directly in the original problem predicate. -/
theorem periodic_inputs_isErdos335Pair_iff {q : ℕ} [NeZero q]
    (A B : Set ℕ) (S T : Finset (ZMod q))
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hA : DensityEquivalent A (periodicSet S))
    (hB : DensityEquivalent B (periodicSet T)) :
    IsErdos335Pair A B ↔
      (baseline A B S T).card = S.card + T.card ∧
        Negligible (((A \ periodicSet S) + (B \ periodicSet T)) \
          periodicSet (baseline A B S T)) := by
  have hAd := hA.symm.hasDensity (hasDensity_periodicSet S)
  have hBd := hB.symm.hasDensity (hasDensity_periodicSet T)
  have hcriterion := periodic_inputs_fringe_criterion A B S T hApos hBpos hS hT hA hB
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  constructor
  · rintro ⟨_, _, a, b, _, _, ha, hb, hsum⟩
    have hae := ha.unique hAd
    have hbe := hb.unique hBd
    apply hcriterion.mp
    simpa only [hae, hbe] using hsum
  · intro h
    refine ⟨hApos, hBpos, (S.card : ℝ) / q, (T.card : ℝ) / q,
      div_pos (by exact_mod_cast hS.card_pos) hq,
      div_pos (by exact_mod_cast hT.card_pos) hq, hAd, hBd, hcriterion.mpr h⟩

end Erdos335
