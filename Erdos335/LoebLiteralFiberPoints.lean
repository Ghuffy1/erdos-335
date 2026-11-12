import Erdos335.QuasiPeriodicSets
import Erdos335.LoebLiteralResidues

/-!
# Actual integer representatives in a nontrivial literal active fiber
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance literalFiberPointsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem internal_literal_fiber_subsingleton
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (A : Set ℕ) (E : ℕ → Set ℕ)
    (hEA : ∀ᶠ n in U, E n ⊆ A) (h : ℕ+)
    (ρ : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ))
    (hρ : ∀ᶠ n in U, ∀ a : ℕ, ρ n (a : ZMod (q n : ℕ)) = (a : ZMod (h : ℕ)))
    (r : ZMod (h : ℕ)) (hsingle : {a : ℕ | a ∈ A ∧ (a : ZMod (h : ℕ)) = r}.Subsingleton) :
    (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) ∩
      (finiteQuotient U ρ) ⁻¹' {r}).Subsingleton := by
  intro x hx y hy
  induction x using Quotient.inductionOn with
  | h f =>
    induction y using Quotient.inductionOn with
    | h g =>
      apply Quotient.sound
      have hf := hx.1
      have hg := hy.1
      change ∀ᶠ n in U, f n ∈ ((↑) : ℕ → ZMod (q n : ℕ)) '' E n at hf
      change ∀ᶠ n in U, g n ∈ ((↑) : ℕ → ZMod (q n : ℕ)) '' E n at hg
      have hfr := hx.2
      have hgr := hy.2
      change finiteValue U (fun n => ρ n (f n)) = r at hfr
      change finiteValue U (fun n => ρ n (g n)) = r at hgr
      have hfe := (finiteValue_eq_iff U _ r).mp hfr
      have hge := (finiteValue_eq_iff U _ r).mp hgr
      filter_upwards [hf, hg, hfe, hge, hEA, hρ] with n hnF hnG hnFr hnGr hnEA hnρ
      obtain ⟨a, ha, haf⟩ := hnF
      obtain ⟨b, hb, hbg⟩ := hnG
      have har : (a : ZMod (h : ℕ)) = r :=
        (hnρ a).symm.trans ((congrArg (ρ n) haf).trans hnFr)
      have hbr : (b : ZMod (h : ℕ)) = r :=
        (hnρ b).symm.trans ((congrArg (ρ n) hbg).trans hnGr)
      have hab : a = b := hsingle ⟨hnEA ha, har⟩ ⟨hnEA hb, hbr⟩
      exact haf.symm.trans ((congrArg (fun v : ℕ => (v : ZMod (q n : ℕ))) hab).trans hbg)

theorem literal_active_has_two_integers
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ℕ) (E : ℕ → Set ℕ) (hEA : ∀ᶠ n in U, E n ⊆ A)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)))
    (hactive : ¬p.active.Subsingleton) (h : ℕ+)
    (ρ : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ))
    (hρ : ∀ᶠ n in U, ∀ a : ℕ, ρ n (a : ZMod (q n : ℕ)) = (a : ZMod (h : ℕ)))
    (hker : (finiteQuotient U ρ).ker = H) :
    ∃ x y : ℕ, x ∈ A ∧ y ∈ A ∧ x < y ∧
      (x : ZMod (h : ℕ)) = finiteQuotient U ρ p.anchor ∧
      (y : ZMod (h : ℕ)) = finiteQuotient U ρ p.anchor := by
  classical
  let C := {a : ℕ | a ∈ A ∧ (a : ZMod (h : ℕ)) = finiteQuotient U ρ p.anchor}
  have hnot : ¬C.Subsingleton := by
    intro hs
    have hf := internal_literal_fiber_subsingleton U q A E hEA h ρ hρ _ hs
    have hsub : p.active ⊆ internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) ∩
        (finiteQuotient U ρ) ⁻¹' {finiteQuotient U ρ p.anchor} := by
      intro x hx
      have hxP : x ∈ internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) :=
        (subset_union_right.trans p.partition.ge) hx
      refine ⟨hxP, ?_⟩
      have hc := p.active_subset_coset hx
      have hc' : x ∈ p.anchor +ᵥ ((finiteQuotient U ρ).ker :
          Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
        simpa only [hker] using hc
      rwa [← addHom_fiber_eq_coset] at hc'
    apply hactive
    intro x hx y hy
    exact hf (hsub hx) (hsub hy)
  have hp : ¬∀ x ∈ C, ∀ y ∈ C, x = y := hnot
  push_neg at hp
  obtain ⟨x, hx, y, hy, hxy⟩ := hp
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact ⟨x, y, hx.1, hy.1, hlt, hx.2, hy.2⟩
  · exact ⟨y, x, hy.1, hx.1, hgt, hy.2, hx.2⟩

end Erdos335.Loeb

end
