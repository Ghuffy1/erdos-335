import Erdos335.StableKneser
import Erdos335.IntegerPeriodicity

/-!
# The integer-density Kneser alternative

The stabilized periodic subset is transported through each actual expression
of an output element. Its density bounds the possible period. A common period
then fills the literal occupied residue classes in the tail.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem periodic_subset_through_zero (A B : Set ℕ)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B) :
    ∃ (P : Set ℕ) (g : ℕ+), P ⊆ A + B ∧ 0 ∈ P ∧
      (∀ᶠ n : ℕ in atTop, n ∈ P ↔ n ∈ periodicSet (residues (g : ℕ) P)) ∧
      jointLowerDensity A B - 1 / (g : ℕ) ≤ lowerDensity P := by
  obtain ⟨C, D, q, hCD, hsep, hstable⟩ :=
    exists_dysonDerived_stable_residues A B hA0 hB0 hgap
  obtain ⟨x, hx, y, hy, hxy, hdiff⟩ := (hstable C D DysonDerived.refl).1
  have hpair : ∃ x ∈ D, ∃ y ∈ D, x < y ∧ y - x ≤ (q : ℕ) :=
    ⟨x, hx, y, hy, hxy, hdiff.le⟩
  have hg := (setGcd_bounds_of_close_pair D q hpair).1
  have hgapCD : lowerDensity (C + D) < jointLowerDensity C D := by
    rw [hCD.jointLowerDensity_eq]
    exact (lowerDensity_mono hCD.sum_subset).trans_lt hgap
  obtain ⟨P, g, hP, hP0, hperiod, hmass⟩ := stable_periodic_subset_through_zero C D q
    (hCD.zero_mem hA0 hB0).1 (hCD.zero_mem hA0 hB0).2 hg hgapCD hstable
  rw [hCD.jointLowerDensity_eq] at hmass
  exact ⟨P, g, hP.trans hCD.sum_subset, hP0, hperiod, hmass⟩

theorem kneser_progression_tail_through_point (A B : Set ℕ)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B)
    {a : ℕ} (ha : a ∈ A + B) :
    ∃ g : ℕ+, (∀ᶠ k : ℕ in atTop, a + (g : ℕ) * k ∈ A + B) ∧
      jointLowerDensity A B - 1 / (g : ℕ) ≤ lowerDensity (A + B) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := ha
  have hA0 : 0 ∈ tailShift A x := by simpa [tailShift] using hx
  have hB0 : 0 ∈ tailShift B y := by simpa [tailShift] using hy
  have hj := jointLowerDensity_tailShift A B x y
  have hsub := shift_tailShift_sum_subset A B x y
  have hl : lowerDensity (tailShift A x + tailShift B y) ≤ lowerDensity (A + B) := by
    rw [← lowerDensity_shift _ (x + y)]
    exact lowerDensity_mono hsub
  have hgap' : lowerDensity (tailShift A x + tailShift B y) <
      jointLowerDensity (tailShift A x) (tailShift B y) := by
    rw [hj]
    exact hl.trans_lt hgap
  obtain ⟨P, g, hP, hP0, hperiod, hmass⟩ :=
    periodic_subset_through_zero (tailShift A x) (tailShift B y) hA0 hB0 hgap'
  rw [hj] at hmass
  refine ⟨g, ?_, hmass.trans ((lowerDensity_mono hP).trans hl)⟩
  have htail := progression_tail_of_literal_periodicity P g hP0 hperiod
  filter_upwards [htail] with k hk
  apply hsub
  refine ⟨(g : ℕ) * k, hP (by simpa using hk), ?_⟩
  exact Nat.add_comm _ _

theorem integer_kneser_alternative (A B : Set ℕ)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) :
    jointLowerDensity A B ≤ lowerDensity (A + B) ∨
      ∃ q : ℕ+, ∀ᶠ n : ℕ in atTop,
        n ∈ A + B ↔ n ∈ periodicSet (residues (q : ℕ) (A + B)) := by
  by_cases hlarge : jointLowerDensity A B ≤ lowerDensity (A + B)
  · exact Or.inl hlarge
  right
  have hgap := lt_of_not_ge hlarge
  have hdelta : 0 < jointLowerDensity A B - lowerDensity (A + B) := sub_pos.mpr hgap
  obtain ⟨D, hD⟩ := exists_nat_gt (1 / (jointLowerDensity A B - lowerDensity (A + B)))
  apply ultimately_periodic_of_bounded_tails (A + B) D (sumset_positive hA hB)
  intro a ha
  obtain ⟨g, htail, hmass⟩ := kneser_progression_tail_through_point A B hgap ha
  have hg0 : (0 : ℝ) < (g : ℕ) := by exact_mod_cast g.pos
  have hfrac : jointLowerDensity A B - lowerDensity (A + B) ≤ 1 / (g : ℕ) := by linarith
  have hproduct := (le_div_iff₀ hg0).mp hfrac
  have hbound : (g : ℕ) ≤ 1 / (jointLowerDensity A B - lowerDensity (A + B)) := by
    apply (le_div_iff₀ hdelta).mpr
    nlinarith
  have hgD : (g : ℕ) ≤ D := by exact_mod_cast (hbound.trans_lt hD).le
  exact ⟨(g : ℕ), g.pos, hgD, htail⟩

theorem density_integer_kneser_alternative {A B : Set ℕ} {a b : ℝ}
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (hAd : HasDensity A a) (hBd : HasDensity B b) :
    a + b ≤ lowerDensity (A + B) ∨
      ∃ q : ℕ+, ∀ᶠ n : ℕ in atTop,
        n ∈ A + B ↔ n ∈ periodicSet (residues (q : ℕ) (A + B)) := by
  have h := integer_kneser_alternative A B hA hB
  rwa [jointLowerDensity_eq_of_hasDensity hAd hBd] at h

theorem hasDensity_sum_of_gamma_eq {A B : Set ℕ} {a b : ℝ}
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (hAd : HasDensity A a) (hBd : HasDensity B b) (hgamma : gamma A B = a + b) :
    HasDensity (A + B) (a + b) :=
  density_sum_of_kneser_alternative hA hB hgamma
    (density_integer_kneser_alternative hA hB hAd hBd)

end Erdos335
