import Erdos335.DysonDensity
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Stabilization of the gcd in a deficient Dyson family

The strict density deficit bounds a gap in every derived right-hand input.
Consequently its gcd is positive and bounded. Maximizing that integer gives a
derived family in which every further derivation has the same gcd.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem DysonDerived.trans {A B C D E F : Set ℕ}
    (h1 : DysonDerived A B C D) (h2 : DysonDerived C D E F) : DysonDerived A B E F := by
  induction h2 with
  | refl => exact h1
  | step h e he ih => exact ih.step e he

theorem exists_bound_on_dyson_gaps (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B) :
    ∃ M : ℕ, 0 < M ∧ ∀ C D : Set ℕ, DysonDerived A B C D →
      ∃ x ∈ D, ∃ y ∈ D, x < y ∧ y - x ≤ M := by
  classical
  by_contra hno
  have hunbounded : ∀ f : ℕ, 0 < f →
      ∃ C D : Set ℕ, DysonDerived A B C D ∧ Separated D f := by
    intro f hf
    by_contra hn
    push Not at hn
    apply hno
    refine ⟨f, hf, ?_⟩
    intro C D hd
    have hs := hn C D hd
    unfold Separated at hs
    push Not at hs
    obtain ⟨x, hx, y, hy, hxy, hdist⟩ := hs
    exact ⟨x, hx, y, hy, hxy, by omega⟩
  exact hgap.not_ge (lowerDensity_sum_ge_of_unbounded_dyson_gaps A B hA hB hunbounded)

theorem setGcd_bounds_of_close_pair (D : Set ℕ) (M : ℕ)
    (hpair : ∃ x ∈ D, ∃ y ∈ D, x < y ∧ y - x ≤ M) :
    0 < Nat.setGcd D ∧ Nat.setGcd D ≤ M := by
  obtain ⟨x, hx, y, hy, hxy, hM⟩ := hpair
  have hgx := Nat.setGcd_dvd_of_mem hx
  have hgy := Nat.setGcd_dvd_of_mem hy
  have hzero : Nat.setGcd D ≠ 0 := by
    intro h
    rw [h] at hgy
    have := zero_dvd_iff.mp hgy
    omega
  have hdist : Nat.setGcd D ∣ y - x := Nat.dvd_sub hgy hgx
  exact ⟨Nat.pos_of_ne_zero hzero, (Nat.le_of_dvd (by omega) hdist).trans hM⟩

theorem exists_dysonDerived_stable_gcd (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B) :
    ∃ C D : Set ℕ, DysonDerived A B C D ∧ 0 < Nat.setGcd D ∧
      ∀ E F : Set ℕ, DysonDerived C D E F → Nat.setGcd F = Nat.setGcd D := by
  classical
  obtain ⟨M, hM, hbound⟩ := exists_bound_on_dyson_gaps A B hA hB hgap
  let P : ℕ → Prop := fun g => ∃ C D : Set ℕ, DysonDerived A B C D ∧ Nat.setGcd D = g
  let g := Nat.findGreatest P M
  have hBbounds := setGcd_bounds_of_close_pair B M (hbound A B DysonDerived.refl)
  have hstart : P (Nat.setGcd B) := ⟨A, B, DysonDerived.refl, rfl⟩
  have hgle : Nat.setGcd B ≤ g := Nat.le_findGreatest hBbounds.2 hstart
  have hgpos : 0 < g := hBbounds.1.trans_le hgle
  have hPg : P g := Nat.findGreatest_of_ne_zero rfl hgpos.ne'
  obtain ⟨C, D, hCD, hDg⟩ := hPg
  refine ⟨C, D, hCD, by simpa only [hDg] using hgpos, ?_⟩
  intro E F hEF
  have hAF := hCD.trans hEF
  have hFbounds := setGcd_bounds_of_close_pair F M (hbound E F hAF)
  have hPF : P (Nat.setGcd F) := ⟨E, F, hAF, rfl⟩
  have hFle : Nat.setGcd F ≤ g := Nat.le_findGreatest hFbounds.2 hPF
  have hdiv : Nat.setGcd D ∣ Nat.setGcd F := Nat.setGcd_mono hEF.right_subset
  have hge : Nat.setGcd D ≤ Nat.setGcd F := Nat.le_of_dvd hFbounds.1 hdiv
  omega

def HasGap (D : Set ℕ) (f : ℕ) : Prop :=
  ∃ x ∈ D, ∃ y ∈ D, x < y ∧ y - x = f

theorem exists_minimum_gap (D : Set ℕ) (M : ℕ)
    (hpair : ∃ x ∈ D, ∃ y ∈ D, x < y ∧ y - x ≤ M) :
    ∃ f : ℕ, 0 < f ∧ f ≤ M ∧ Separated D f ∧ HasGap D f := by
  classical
  obtain ⟨x, hx, y, hy, hxy, hM⟩ := hpair
  have hex : ∃ f : ℕ, HasGap D f := ⟨y - x, x, hx, y, hy, hxy, rfl⟩
  let f := Nat.find hex
  have hf : HasGap D f := Nat.find_spec hex
  obtain ⟨a, ha, b, hb, hab, hfval⟩ := hf
  have hfpos : 0 < f := by omega
  have hfle : f ≤ y - x := Nat.find_min' hex ⟨x, hx, y, hy, hxy, rfl⟩
  refine ⟨f, hfpos, hfle.trans hM, ?_, a, ha, b, hb, hab, hfval⟩
  intro u hu v hv huv
  exact Nat.find_min' hex ⟨u, hu, v, hv, huv, rfl⟩

theorem Separated.mono_set {C D : Set ℕ} {f : ℕ}
    (h : Separated D f) (hCD : C ⊆ D) : Separated C f := by
  intro x hx y hy hxy
  exact h x (hCD hx) y (hCD hy) hxy

theorem exists_dysonDerived_stable_gap (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B) :
    ∃ (C D : Set ℕ) (f : ℕ), DysonDerived A B C D ∧ 0 < f ∧ Separated D f ∧
      ∀ E F : Set ℕ, DysonDerived C D E F →
        HasGap F f ∧ Nat.setGcd F = Nat.setGcd D := by
  classical
  obtain ⟨C₀, D₀, h₀, hgpos, hstable⟩ := exists_dysonDerived_stable_gcd A B hA hB hgap
  obtain ⟨M, hMpos, hbound⟩ := exists_bound_on_dyson_gaps A B hA hB hgap
  let P : ℕ → Prop := fun f => ∃ C D : Set ℕ,
    DysonDerived C₀ D₀ C D ∧ Separated D f ∧ HasGap D f
  obtain ⟨f₀, hf₀pos, hf₀M, hf₀sep, hf₀gap⟩ :=
    exists_minimum_gap D₀ M (hbound C₀ D₀ h₀)
  let f := Nat.findGreatest P M
  have hf₀P : P f₀ := ⟨C₀, D₀, DysonDerived.refl, hf₀sep, hf₀gap⟩
  have hf₀le : f₀ ≤ f := Nat.le_findGreatest hf₀M hf₀P
  have hfpos : 0 < f := hf₀pos.trans_le hf₀le
  have hfP : P f := Nat.findGreatest_of_ne_zero rfl hfpos.ne'
  obtain ⟨C, D, hCD, hsep, hfgap⟩ := hfP
  refine ⟨C, D, f, h₀.trans hCD, hfpos, hsep, ?_⟩
  intro E F hEF
  have hCF := hCD.trans hEF
  obtain ⟨f', hf'pos, hf'M, hf'sep, hf'gap⟩ :=
    exists_minimum_gap F M (hbound E F (h₀.trans hCF))
  have hf'P : P f' := ⟨E, F, hCF, hf'sep, hf'gap⟩
  have hle : f' ≤ f := Nat.le_findGreatest hf'M hf'P
  obtain ⟨x, hx, y, hy, hxy, hf'val⟩ := hf'gap
  have hge : f ≤ f' := hf'val ▸ (hsep.mono_set hEF.right_subset) x hx y hy hxy
  have heq : f' = f := le_antisymm hle hge
  constructor
  · exact ⟨x, hx, y, hy, hxy, hf'val.trans heq⟩
  · exact (hstable E F hCF).trans (hstable C D hCD).symm

theorem exists_dysonDerived_stable_residues (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B) :
    ∃ (C D : Set ℕ) (q : ℕ+), DysonDerived A B C D ∧ Separated D q ∧
      ∀ E F : Set ℕ, DysonDerived C D E F → HasGap F q ∧
        Nat.setGcd F = Nat.setGcd D ∧ residues (q : ℕ) F = residues (q : ℕ) D := by
  classical
  obtain ⟨C₀, D₀, f, h₀, hfpos, hsep, hstable⟩ :=
    exists_dysonDerived_stable_gap A B hA hB hgap
  let q : ℕ+ := ⟨f, hfpos⟩
  let P : ℕ → Prop := fun n => ∃ C D : Set ℕ,
    DysonDerived C₀ D₀ C D ∧ (residues (q : ℕ) D).card = n
  have hex : ∃ n : ℕ, P n := ⟨(residues (q : ℕ) D₀).card, C₀, D₀, DysonDerived.refl, rfl⟩
  obtain ⟨C, D, hCD, hcard⟩ := Nat.find_spec hex
  have hsepD : Separated D q := hsep.mono_set hCD.right_subset
  refine ⟨C, D, q, h₀.trans hCD, hsepD, ?_⟩
  intro E F hEF
  have hCF := hCD.trans hEF
  obtain ⟨hfgap, hgF⟩ := hstable E F hCF
  have hgD := (hstable C D hCD).2
  refine ⟨hfgap, hgF.trans hgD.symm, ?_⟩
  have hsub : residues (q : ℕ) F ⊆ residues (q : ℕ) D := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := mem_residues.mp hr
    exact mem_residues.mpr ⟨x, hEF.right_subset hx, hxr⟩
  have hPF : P (residues (q : ℕ) F).card := ⟨E, F, hCF, rfl⟩
  have hmin := Nat.find_min' hex hPF
  apply Finset.eq_of_subset_of_card_le hsub
  omega

end Erdos335
