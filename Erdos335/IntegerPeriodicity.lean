import Erdos335.LowerDensity
import Mathlib.Data.Nat.Factorial.Basic

/-!
# From bounded progression tails to eventual periodicity

This is the finite-period step in Kneser's original reduction from Proposition
III to Proposition I. The pointwise progression-tail hypothesis remains an
explicit hypothesis here.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem ultimately_periodic_of_bounded_tails (C : Set ℕ) (D : ℕ)
    (hCpos : C ⊆ Set.Ioi 0)
    (htails : ∀ a ∈ C, ∃ g : ℕ, 0 < g ∧ g ≤ D ∧
      ∀ᶠ k : ℕ in atTop, a + g * k ∈ C) :
    ∃ q : ℕ+, ∀ᶠ n : ℕ in atTop, n ∈ C ↔ n ∈ periodicSet (residues (q : ℕ) C) := by
  classical
  let q : ℕ+ := ⟨D.factorial, Nat.factorial_pos D⟩
  have hclasses : ∀ r ∈ residues (q : ℕ) C, ∀ᶠ n : ℕ in atTop,
      (n : ZMod (q : ℕ)) = r → n ∈ C := by
    intro r hr
    obtain ⟨a, ha, har⟩ := mem_residues.mp hr
    obtain ⟨g, hg0, hgD, htail⟩ := htails a ha
    obtain ⟨K, hK⟩ := eventually_atTop.mp htail
    have hgdvd : g ∣ (q : ℕ) := Nat.dvd_factorial hg0 hgD
    filter_upwards [eventually_ge_atTop (a + g * K)] with n hn
    intro hnr
    have hmod : Nat.ModEq (q : ℕ) a n :=
      (ZMod.natCast_eq_natCast_iff a n (q : ℕ)).mp (har.trans hnr.symm)
    have hdiv : g ∣ n - a := (hmod.of_dvd hgdvd).dvd'
    have han : a ≤ n := by omega
    have hk : K ≤ (n - a) / g := by
      apply (Nat.le_div_iff_mul_le hg0).mpr
      rw [Nat.mul_comm K g]
      omega
    have hrep : a + g * ((n - a) / g) = n := by
      rw [Nat.mul_div_cancel' hdiv]
      exact Nat.add_sub_of_le han
    simpa only [hrep] using hK ((n - a) / g) hk
  have hall := (residues (q : ℕ) C).eventually_all.mpr hclasses
  refine ⟨q, ?_⟩
  filter_upwards [hall] with n hn
  constructor
  · intro hnC
    exact ⟨hCpos hnC, mem_residues.mpr ⟨n, hnC, rfl⟩⟩
  · rintro ⟨hn0, hnr⟩
    exact hn (n : ZMod (q : ℕ)) hnr rfl

theorem density_of_bounded_tails (C : Set ℕ) (D : ℕ)
    (hCpos : C ⊆ Set.Ioi 0)
    (htails : ∀ a ∈ C, ∃ g : ℕ, 0 < g ∧ g ≤ D ∧
      ∀ᶠ k : ℕ in atTop, a + g * k ∈ C) :
    ∃ q : ℕ+, HasDensity C (((residues (q : ℕ) C).card : ℝ) / q) := by
  obtain ⟨q, hq⟩ := ultimately_periodic_of_bounded_tails C D hCpos htails
  obtain ⟨K, hK⟩ := eventually_atTop.mp hq
  refine ⟨q, (hasDensity_periodicSet (residues (q : ℕ) C)).of_eventually_eq K ?_⟩
  intro n hn
  exact (hK n hn.le).symm

theorem density_sum_of_bounded_tails (A B : Set ℕ) (D : ℕ)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (htails : ∀ a ∈ A + B, ∃ g : ℕ, 0 < g ∧ g ≤ D ∧
      ∀ᶠ k : ℕ in atTop, a + g * k ∈ A + B) :
    HasDensity (A + B) (gamma A B) := by
  have hCpos : A + B ⊆ Set.Ioi 0 := by
    rintro n ⟨a, ha, b, hb, rfl⟩
    have ha0 : 0 < a := hA ha
    have hb0 : 0 < b := hB hb
    change 0 < a + b
    omega
  obtain ⟨q, hq⟩ := density_of_bounded_tails (A + B) D hCpos htails
  have hlow := density_sum_le_gamma hA hB hq
  have hbound : BddBelow (Set.range (modularCapacity A B)) :=
    ⟨0, by rintro d ⟨q, rfl⟩; exact modularCapacity_nonneg A B q⟩
  have hupp := ciInf_le hbound q
  rw [modularCapacity, ← residues_add] at hupp
  rw [le_antisymm hlow hupp] at hq
  exact hq

theorem progression_tail_of_literal_periodicity (E : Set ℕ) (q : ℕ+) {a : ℕ}
    (ha : a ∈ E)
    (hE : ∀ᶠ n : ℕ in atTop, n ∈ E ↔ n ∈ periodicSet (residues (q : ℕ) E)) :
    ∀ᶠ k : ℕ in atTop, a + (q : ℕ) * k ∈ E := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hE
  filter_upwards [eventually_ge_atTop (K + 1)] with k hk
  have hq0 := q.pos
  have hkg : k ≤ (q : ℕ) * k := by nlinarith
  apply (hK (a + (q : ℕ) * k) (by omega)).mpr
  refine ⟨by nlinarith, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] using
    (mem_residues.mpr ⟨a, ha, rfl⟩ : (a : ZMod (q : ℕ)) ∈ residues (q : ℕ) E)

/-- The reduction from Kneser's pointwise periodic-subset assertion to his
literal periodicity alternative. The pointwise assertion is a hypothesis. -/
theorem ultimately_periodic_of_periodic_subsets (C : Set ℕ) (s : ℝ)
    (hCpos : C ⊆ Set.Ioi 0) (hgap : lowerDensity C < s)
    (hsubsets : ∀ a ∈ C, ∃ (E : Set ℕ) (q : ℕ+),
      E ⊆ C ∧ a ∈ E ∧
      (∀ᶠ n : ℕ in atTop, n ∈ E ↔ n ∈ periodicSet (residues (q : ℕ) E)) ∧
      s - 1 / (q : ℕ) ≤ lowerDensity E) :
    ∃ q : ℕ+, ∀ᶠ n : ℕ in atTop, n ∈ C ↔ n ∈ periodicSet (residues (q : ℕ) C) := by
  have hdelta : 0 < s - lowerDensity C := sub_pos.mpr hgap
  obtain ⟨D, hD⟩ := exists_nat_gt (1 / (s - lowerDensity C))
  apply ultimately_periodic_of_bounded_tails C D hCpos
  intro a ha
  obtain ⟨E, q, hEC, haE, hperiod, hmass⟩ := hsubsets a ha
  have hmass' := hmass.trans (lowerDensity_mono hEC)
  have hq0 : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  have hfrac : s - lowerDensity C ≤ 1 / (q : ℕ) := by linarith
  have hproduct := (le_div_iff₀ hq0).mp hfrac
  have hbound : (q : ℕ) ≤ 1 / (s - lowerDensity C) := by
    apply (le_div_iff₀ hdelta).mpr
    nlinarith
  have hqD : (q : ℕ) ≤ D := by exact_mod_cast (hbound.trans_lt hD).le
  refine ⟨(q : ℕ), q.pos, hqD, ?_⟩
  exact (progression_tail_of_literal_periodicity E q haE hperiod).mono fun k hk => hEC hk

theorem density_sum_of_kneser_alternative {A B : Set ℕ} {s : ℝ}
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) (hgamma : gamma A B = s)
    (hKneser : s ≤ lowerDensity (A + B) ∨
      ∃ q : ℕ+, ∀ᶠ n : ℕ in atTop,
        n ∈ A + B ↔ n ∈ periodicSet (residues (q : ℕ) (A + B))) :
    HasDensity (A + B) s := by
  rcases hKneser with hl | ⟨q, hq⟩
  · rw [← hgamma] at hl ⊢
    exact density_sum_of_lowerDensity_ge_gamma hA hB hl
  · obtain ⟨K, hK⟩ := eventually_atTop.mp hq
    have hd := (hasDensity_periodicSet (residues (q : ℕ) (A + B))).of_eventually_eq K
      (fun n hn => (hK n hn.le).symm)
    have hlo := density_sum_le_gamma hA hB hd
    have hbound : BddBelow (Set.range (modularCapacity A B)) :=
      ⟨0, by rintro d ⟨q, rfl⟩; exact modularCapacity_nonneg A B q⟩
    have hup := ciInf_le hbound q
    rw [modularCapacity, ← residues_add] at hup
    rw [le_antisymm hlo hup, hgamma] at hd
    exact hd

end Erdos335
