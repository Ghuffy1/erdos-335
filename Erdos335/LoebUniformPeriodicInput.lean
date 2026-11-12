import Erdos335.LoebCommonNullPeriods
import Erdos335.LoebIntegerPeriods
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Fixed periods and finite covers for periodic actual input windows

Private proof development. Verification status is recorded separately.
The period and the two finite sets are chosen before the ultrafilter, the
cyclic orders, the window starts, and the input mask.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335

theorem exists_finite_bounded_residue_representatives (A : Set ℕ) (N : ℕ) :
    ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∀ h : ℕ+, (h : ℕ) ≤ N →
        ∀ r ∈ residues (h : ℕ) A, ∃ u ∈ F, (u : ZMod (h : ℕ)) = r := by
  classical
  let k : ℕ+ := ⟨N.factorial, Nat.factorial_pos N⟩
  obtain ⟨F, hF, hrep⟩ := exists_finite_residue_representatives A k
  refine ⟨F, hF, ?_⟩
  intro h hN r hr
  have hdk : (h : ℕ) ∣ (k : ℕ) := Nat.dvd_factorial h.pos hN
  obtain ⟨n, hn, hnr⟩ := mem_residues.mp hr
  obtain ⟨u, hu, hun⟩ := hrep (n : ZMod (k : ℕ)) (mem_residues.mpr ⟨n, hn, rfl⟩)
  refine ⟨u, hu, ?_⟩
  have hp := congrArg (Loeb.naturalCyclicProjection k h) hun
  rw [Loeb.naturalCyclicProjection_natCast k h hdk u,
    Loeb.naturalCyclicProjection_natCast k h hdk n] at hp
  exact hp.trans hnr

namespace Loeb

local instance uniformPeriodicInputLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_uniform_periodic_input_witnesses
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hgap : a + b < gamma A B)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) :
    ∃ (M : ℕ+) (FA FB : Finset ℕ), (FA : Set ℕ) ⊆ A ∧ (FB : Set ℕ) ⊆ B ∧
      ∀ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+),
        (∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) →
        Tendsto (fun n => (q n : ℕ)) atTop atTop →
        ∀ start : ℕ → ℕ,
          (loebMeasure U hU (internalSet U
            (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a →
          (loebMeasure U hU (internalSet U
            (fun n => (cyclicWindow B (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b →
          (loebMeasure U hU (internalSet U
            (fun n => (cyclicWindow (A + B) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b →
          ∀ (m : ℕ+) (P : Finset (ZMod (m : ℕ))),
            ((∀ r, actualWindowProfile U hU q m A start r = if r ∈ P then (1 : ℝ) else 0) ∨
              (∀ r, actualWindowProfile U hU q m B start r = if r ∈ P then (1 : ℝ) else 0)) →
            ∃ h : ℕ+, (h : ℕ) ∣ (m : ℕ) ∧
              ((h : ℕ) : ℝ) ≤ max (1 / δA) (max (1 / δB) (1 / (gamma A B - (a + b)))) ∧
              (ActualWindowNullFrame U hU q h A B start a ∨
                ActualWindowNullFrame U hU q h B A start b) ∧
              let W := fun E : Set ℕ => internalSet U
                (fun n => (cyclicWindow E (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
              let t := productProjection (U : Filter ℕ) (fun n => ((M : ℕ) : ZMod (q n : ℕ)))
              (t +ᵥ W A =ᵐ[loebMeasure U hU] W A) ∧
              (t +ᵥ W B =ᵐ[loebMeasure U hU] W B) ∧
              (t +ᵥ W (A + B) =ᵐ[loebMeasure U hU] W (A + B)) ∧
              W (A + B) =ᵐ[loebMeasure U hU] W (Proposed.finiteTranslateCover A B FA FB) := by
  classical
  let bound := max (1 / δA) (max (1 / δB) (1 / (gamma A B - (a + b))))
  let N := Nat.ceil bound
  obtain ⟨DA, hDA, hperiodA⟩ := exists_uniform_common_null_periods A a δA hδA hcapA
  obtain ⟨DB, hDB, hperiodB⟩ := exists_uniform_common_null_periods B b δB hδB hcapB
  let D := DA ∪ DB
  have hD : ∀ t ∈ D, 0 < t := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact hDA t ht
    · exact hDB t ht
  let M : ℕ+ := ⟨(D.sup id).factorial, Nat.factorial_pos (D.sup id)⟩
  have hdivM (t : ℕ) (ht : t ∈ D) : t ∣ (M : ℕ) :=
    Nat.dvd_factorial (hD t ht) (Finset.le_sup (f := id) ht)
  obtain ⟨FA, hFA, hrepA⟩ := exists_finite_bounded_residue_representatives A N
  obtain ⟨FB, hFB, hrepB⟩ := exists_finite_bounded_residue_representatives B N
  refine ⟨M, FA, FB, hFA, hFB, ?_⟩
  intro U hU q hdiv hq start hmA hmB hmC m P hP
  have hswap : gamma B A = gamma A B := by
    unfold gamma modularCapacity
    simp only [add_comm]
  have hmSwap : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (B + A) (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b + a := by
    simpa only [add_comm B A, add_comm b a] using hmC
  have hframe : ∃ h : ℕ+, (h : ℕ) ∣ (m : ℕ) ∧ ((h : ℕ) : ℝ) ≤ bound ∧
      (ActualWindowNullFrame U hU q h A B start a ∨
        ActualWindowNullFrame U hU q h B A start b) := by
    rcases hP with hP | hP
    · exact periodic_input_has_bounded_null_frame U hU q hdiv hq A B start a b δA δB
        ha hb hδA hδB hmA hmB hmC hgap hcapA hcapB m P hP
    · obtain ⟨h, hd, hbnd, hf⟩ := periodic_input_has_bounded_null_frame U hU q hdiv hq
        B A start b a δB δA hb ha hδB hδA hmB hmA hmSwap
        (by simpa only [hswap, add_comm b a] using hgap) hcapB hcapA m P hP
      have hbnd' : ((h : ℕ) : ℝ) ≤ bound := by
        simpa only [hswap, add_comm b a, max_left_comm] using hbnd
      exact ⟨h, hd, hbnd', hf.symm⟩
  obtain ⟨h, hd, hbnd, hf⟩ := hframe
  have hN : (h : ℕ) ≤ N := by
    exact_mod_cast hbnd.trans (Nat.le_ceil bound)
  let W := fun E : Set ℕ => internalSet U
    (fun n => (cyclicWindow E (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  let point := fun t : ℕ => productProjection (U : Filter ℕ) (fun n => (t : ZMod (q n : ℕ)))
  have lift (E : Set ℕ) (t : ℕ) (ht : t ∈ D)
      (hperiod : point t +ᵥ W E =ᵐ[loebMeasure U hU] W E) :
      point (M : ℕ) +ᵥ W E =ᵐ[loebMeasure U hU] W E := by
    have hMt := hdivM t ht
    have hp := loeb_period_nsmul U hU q (W E) (point t) hperiod ((M : ℕ) / t)
    have hmul : ((M : ℕ) / t) * t = (M : ℕ) := by
      simpa only [Nat.mul_comm] using Nat.mul_div_cancel' hMt
    rw [← productProjection_nat_mul, hmul] at hp
    exact hp
  have hdata : (point (M : ℕ) +ᵥ W A =ᵐ[loebMeasure U hU] W A) ∧
      (point (M : ℕ) +ᵥ W B =ᵐ[loebMeasure U hU] W B) ∧
      (point (M : ℕ) +ᵥ W (A + B) =ᵐ[loebMeasure U hU] W (A + B)) ∧
      W (A + B) =ᵐ[loebMeasure U hU] W (Proposed.finiteTranslateCover A B FA FB) := by
    rcases hf with hf | hf
    · obtain ⟨t, ht, hA, hB, hC⟩ := hperiodA U hU q hq h (hdiv h) B start b hf hmA hmB hmC
      have htD : t ∈ D := Finset.mem_union.mpr (Or.inl ht)
      exact ⟨lift A t htD hA, lift B t htD hB, lift (A + B) t htD hC,
        ActualWindowNullFrame.finite_coverage U hU q hq h (hdiv h) A B start a b hf hmB hmC
          FA FB hFA hFB (hrepA h hN) (hrepB h hN)⟩
    · obtain ⟨t, ht, hB, hA, hC⟩ := hperiodB U hU q hq h (hdiv h) A start a hf hmB hmA hmSwap
      have htD : t ∈ D := Finset.mem_union.mpr (Or.inr ht)
      have hC' : point t +ᵥ W (A + B) =ᵐ[loebMeasure U hU] W (A + B) := by
        simpa only [add_comm B A] using hC
      have hcover := ActualWindowNullFrame.finite_coverage U hU q hq h (hdiv h) B A start b a hf hmA hmSwap
        FB FA hFB hFA (hrepB h hN) (hrepA h hN)
      refine ⟨lift A t htD hA, lift B t htD hB, lift (A + B) t htD hC', ?_⟩
      simpa only [add_comm B A, Proposed.finiteTranslateCover, Set.union_comm] using hcover
  exact ⟨h, hd, hbnd, hf, hdata⟩

end Loeb

end Erdos335

end
