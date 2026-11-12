import Erdos335.PeriodicInputs

/-!
# Periodic output in the strict Buck-surplus case

Residue fibers are selected by failure of density-zero negligibility. Their
individual densities need not exist. This gives the converse periodic reduction
without a residue-density assumption on either input.

This formalizes the periodic-output converse in the owner packet
`lemmas_20261110T2218Z.md` and the saturated-baseline branch of
`periodic_summand_exact_reduction_20261110T2330Z.md`.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem hasDensity_shift_iff (A : Set ℕ) (t : ℕ) (d : ℝ) :
    HasDensity (shift A t) d ↔ HasDensity A d := by
  constructor
  · intro hshift
    have hdiff : Tendsto (fun N => ((count A N : ℝ) - count (shift A t) N) / N)
        atTop (𝓝 0) := by
      have h := tendsto_div_of_bounded
        (fun N => (count A N : ℝ) - count (shift A t) N) 0 (t + 1)
        (fun N => by simpa only [zero_mul, sub_zero, abs_sub_comm] using count_shift_error A N t)
      simpa only [zero_mul, sub_zero] using h
    have hlim := hshift.add hdiff
    simp only [add_zero] at hlim
    apply hlim.congr
    intro N
    ring
  · exact fun h => h.shift t

theorem negligible_shift_iff (A : Set ℕ) (t : ℕ) :
    Negligible (shift A t) ↔ Negligible A := hasDensity_shift_iff A t 0

theorem gamma_le_modularCapacity (A B : Set ℕ) (q : ℕ+) :
    gamma A B ≤ modularCapacity A B q := by
  apply ciInf_le
  refine ⟨0, ?_⟩
  rintro x ⟨r, rfl⟩
  exact modularCapacity_nonneg A B r

theorem gamma_le_of_residue_sum_subset {q : ℕ} [NeZero q]
    (A B : Set ℕ) (U : Finset (ZMod q))
    (h : residues q A + residues q B ⊆ U) : gamma A B ≤ (U.card : ℝ) / q := by
  let qp : ℕ+ := ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩
  apply (gamma_le_modularCapacity A B qp).trans
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card h) (Nat.cast_nonneg q)

def residueFiber {q : ℕ} (A : Set ℕ) (r : ZMod q) : Set ℕ :=
  A ∩ periodicSet ({r} : Finset (ZMod q))

noncomputable def positiveResidues (q : ℕ) [NeZero q] (A : Set ℕ) : Finset (ZMod q) := by
  classical
  exact Finset.univ.filter (fun r => ¬Negligible (residueFiber A r))

@[simp] theorem mem_positiveResidues {q : ℕ} [NeZero q] {A : Set ℕ} {r : ZMod q} :
    r ∈ positiveResidues q A ↔ ¬Negligible (residueFiber A r) := by
  classical
  simp [positiveResidues]

theorem positiveResidues_subset_residues (q : ℕ) [NeZero q] (A : Set ℕ) :
    positiveResidues q A ⊆ residues q A := by
  intro r hr
  by_contra hmissing
  apply mem_positiveResidues.mp hr
  apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
  rintro n ⟨hnA, hnR⟩
  have hnr : (n : ZMod q) = r := by simpa using hnR.2
  exact (hmissing (mem_residues.mpr ⟨n, hnA, hnr⟩)).elim

theorem outside_positiveResidues_negligible (q : ℕ) [NeZero q]
    (A : Set ℕ) (hA : A ⊆ Set.Ioi 0) :
    Negligible (A \ periodicSet (positiveResidues q A)) := by
  classical
  let F := Finset.univ \ positiveResidues q A
  have hf : ∀ r ∈ F, Negligible (residueFiber A r) := by
    intro r hr
    have hnot := (Finset.mem_sdiff.mp hr).2
    by_contra h
    exact hnot (mem_positiveResidues.mpr h)
  apply (negligible_finiteUnion F (residueFiber A) hf).mono
  rintro n ⟨hnA, hnP⟩
  have hn0 : 0 < n := hA hnA
  refine ⟨(n : ZMod q), ?_, ⟨hnA, hn0, by simp⟩⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact fun hr => hnP ⟨hn0, hr⟩

theorem positiveResidues_nonempty (q : ℕ) [NeZero q]
    (A : Set ℕ) (hA : A ⊆ Set.Ioi 0) {a : ℝ} (ha : HasDensity A a) (ha0 : 0 < a) :
    (positiveResidues q A).Nonempty := by
  classical
  by_contra h
  have hemp : positiveResidues q A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hzero := outside_positiveResidues_negligible q A hA
  have hA0 : HasDensity A 0 := by simpa [hemp, periodicSet, Negligible] using hzero
  have heq := ha.unique hA0
  linarith

theorem density_le_positiveResidues_card (q : ℕ) [NeZero q]
    (A : Set ℕ) (hA : A ⊆ Set.Ioi 0) {a : ℝ} (ha : HasDensity A a) :
    a ≤ ((positiveResidues q A).card : ℝ) / q := by
  have houtside := outside_positiveResidues_negligible q A hA
  have hnonneg := (hasDensity_periodicSet (positiveResidues q A)).sdiff_of_negligible_reverse
    ha houtside
  have h := hnonneg.nonneg
  linarith

theorem shift_fiber_subset_outside {q : ℕ} [NeZero q]
    {A B : Set ℕ} {r : ZMod q} {b : ℕ} (hb : b ∈ B)
    (U : Finset (ZMod q)) (hmissing : r + (b : ZMod q) ∉ U) :
    shift (residueFiber A r) b ⊆ (A + B) \ periodicSet U := by
  rintro n ⟨a, ha, rfl⟩
  have har : (a : ZMod q) = r := by simpa using ha.2.2
  refine ⟨⟨a, ha.1, b, hb, rfl⟩, ?_⟩
  intro hn
  apply hmissing
  simpa only [Nat.cast_add, har] using hn.2

theorem positive_cross_subset {q : ℕ} [NeZero q]
    (A B : Set ℕ) (U : Finset (ZMod q))
    (hC : Negligible ((A + B) \ periodicSet U)) :
    positiveResidues q A + residues q B ⊆ U := by
  intro w hw
  obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hw
  obtain ⟨b, hb, rfl⟩ := mem_residues.mp ht
  by_contra hmissing
  have hzero := hC.mono (shift_fiber_subset_outside hb U hmissing)
  exact (mem_positiveResidues.mp hr) ((negligible_shift_iff _ b).mp hzero)

/-- Periodic output at a strict Buck surplus forces both inputs to be periodic in density. -/
theorem periodic_output_forces_periodic_inputs {q : ℕ} [NeZero q]
    (A B : Set ℕ) (U : Finset (ZMod q)) (a b : ℝ)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (ha0 : 0 < a) (hb0 : 0 < b)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (hCU : DensityEquivalent (A + B) (periodicSet U))
    (hgap : a + b < gamma A B) :
    ∃ P Q : Finset (ZMod q), P.Nonempty ∧ Q.Nonempty ∧
      DensityEquivalent A (periodicSet P) ∧ DensityEquivalent B (periodicSet Q) ∧
      U = baseline A B P Q ∧ U.card = P.card + Q.card := by
  classical
  let P := positiveResidues q A
  let Q := positiveResidues q B
  have hP : P.Nonempty := positiveResidues_nonempty q A hApos hA ha0
  have hQ : Q.Nonempty := positiveResidues_nonempty q B hBpos hB hb0
  have hPA : P ⊆ residues q A := positiveResidues_subset_residues q A
  have hQB : Q ⊆ residues q B := positiveResidues_subset_residues q B
  have hPT : P + residues q B ⊆ U := positive_cross_subset A B U hCU.1
  have hSQ : residues q A + Q ⊆ U := by
    have h := positive_cross_subset B A U (by simpa only [add_comm] using hCU.1)
    simpa only [add_comm] using h
  have hcore : P + Q ⊆ U :=
    (Finset.add_subset_add (Finset.Subset.refl P) hQB).trans hPT
  have hPout : Negligible (A \ periodicSet P) := outside_positiveResidues_negligible q A hApos
  have hQout : Negligible (B \ periodicSet Q) := outside_positiveResidues_negligible q B hBpos
  have hap : a ≤ (P.card : ℝ) / q := density_le_positiveResidues_card q A hApos hA
  have hbq : b ≤ (Q.card : ℝ) / q := density_le_positiveResidues_card q B hBpos hB
  have hsum : a + b = (U.card : ℝ) / q :=
    hC.unique (hCU.symm.hasDensity (hasDensity_periodicSet U))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hcardLe : U.card ≤ P.card + Q.card := by
    have hdiv : (U.card : ℝ) / q ≤ ((P.card : ℝ) + Q.card) / q := by
      rw [add_div, ← hsum]
      linarith
    have hmul := (div_le_div_iff₀ hqpos hqpos).mp hdiv
    have hr : (U.card : ℝ) ≤ (P.card : ℝ) + Q.card := by nlinarith
    exact_mod_cast hr
  have hcardGe : P.card + Q.card ≤ U.card := by
    by_contra h
    have hsmall : U.card < P.card + Q.card := by omega
    have hfull := FiniteKneser.extended_support_sum_subset hP hQ hcore hSQ hPT hsmall
    have hbound := gamma_le_of_residue_sum_subset A B U (hfull.trans hcore)
    rw [← hsum] at hbound
    exact (not_lt_of_ge hbound) hgap
  have hcard : U.card = P.card + Q.card := by omega
  have hmass : a + b = (P.card : ℝ) / q + (Q.card : ℝ) / q := by
    simpa only [hcard, Nat.cast_add, add_div] using hsum
  have hae : a = (P.card : ℝ) / q := by linarith
  have hbe : b = (Q.card : ℝ) / q := by linarith
  have hAE : DensityEquivalent A (periodicSet P) := by
    refine ⟨hPout, ?_⟩
    have hd := (hasDensity_periodicSet P).sdiff_of_negligible_reverse hA hPout
    change HasDensity (periodicSet P \ A) 0
    simpa only [hae, sub_self] using hd
  have hBE : DensityEquivalent B (periodicSet Q) := by
    refine ⟨hQout, ?_⟩
    have hd := (hasDensity_periodicSet Q).sdiff_of_negligible_reverse hB hQout
    change HasDensity (periodicSet Q \ B) 0
    simpa only [hbe, sub_self] using hd
  have hbaseline : baseline A B P Q ⊆ U := Finset.union_subset hSQ hPT
  have hcriterion := (periodic_inputs_criterion A B P Q hApos hBpos hP hQ hAE hBE).mp
    (by simpa only [hae, hbe] using hC)
  have hbaselineCard : (baseline A B P Q).card = U.card := by omega
  have hEq : baseline A B P Q = U :=
    Finset.eq_of_subset_of_card_le hbaseline hbaselineCard.ge
  exact ⟨P, Q, hP, hQ, hAE, hBE, hEq.symm, hcard⟩

/-- The same reduction with the literal escaping fringe retained explicitly. -/
theorem periodic_output_reduction {q : ℕ} [NeZero q]
    (A B : Set ℕ) (U : Finset (ZMod q)) (a b : ℝ)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (ha0 : 0 < a) (hb0 : 0 < b)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (hCU : DensityEquivalent (A + B) (periodicSet U))
    (hgap : a + b < gamma A B) :
    ∃ P Q : Finset (ZMod q), P.Nonempty ∧ Q.Nonempty ∧
      DensityEquivalent A (periodicSet P) ∧ DensityEquivalent B (periodicSet Q) ∧
      U = baseline A B P Q ∧ U.card = P.card + Q.card ∧
      Negligible (((A \ periodicSet P) + (B \ periodicSet Q)) \ periodicSet U) := by
  obtain ⟨P, Q, hP, hQ, hAE, hBE, hU, hcard⟩ :=
    periodic_output_forces_periodic_inputs A B U a b hApos hBpos ha0 hb0 hA hB hC hCU hgap
  refine ⟨P, Q, hP, hQ, hAE, hBE, hU, hcard, ?_⟩
  have h := hCU.1
  rw [hU, escaping_sum_eq q A B hApos hBpos P Q] at h
  simpa only [hU] using h

/-- When the one-periodic-input baseline has the whole output mass, the converse applies. -/
theorem one_periodic_saturated_baseline {q : ℕ} [NeZero q]
    (A B : Set ℕ) (T : Finset (ZMod q)) (a b : ℝ)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (ha0 : 0 < a) (hb0 : 0 < b)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (hBT : DensityEquivalent B (periodicSet T))
    (hgap : a + b < gamma A B)
    (hsat : a + b = ((residues q A + T).card : ℝ) / q) :
    ∃ P Q : Finset (ZMod q), P.Nonempty ∧ Q.Nonempty ∧
      DensityEquivalent A (periodicSet P) ∧ DensityEquivalent B (periodicSet Q) ∧
      residues q A + T = baseline A B P Q ∧
      (residues q A + T).card = P.card + Q.card := by
  let W := residues q A + T
  change a + b = (W.card : ℝ) / q at hsat
  have hhole : Negligible (periodicSet W \ (A + B)) := by
    apply negligible_periodic_diff_of_singletons
    intro w hw
    exact missing_left_baseline_singleton hBT hw
  have hout := hC.sdiff_of_negligible_reverse (hasDensity_periodicSet W) hhole
  have hout0 : Negligible ((A + B) \ periodicSet W) := by
    change HasDensity ((A + B) \ periodicSet W) 0
    simpa only [hsat, sub_self] using hout
  exact periodic_output_forces_periodic_inputs A B W a b hApos hBpos ha0 hb0 hA hB hC
    ⟨hout0, hhole⟩ hgap

end Erdos335
