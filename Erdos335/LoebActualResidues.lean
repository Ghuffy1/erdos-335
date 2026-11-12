import Erdos335.LoebFiniteResidueProfiles
import Erdos335.CyclicWindowRepresentatives

/-!
# Literal integer residues of an actual window model
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped BigOperators ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance actualResiduesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem actual_residue_of_internal_cyclic_window
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (x : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hx : x ∈ internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) :
    finiteQuotient U (fun n => naturalCyclicProjection (q n) h) x +
      finiteValue U (fun n => (start n : ZMod (h : ℕ))) ∈ residues (h : ℕ) A := by
  classical
  induction x using Quotient.inductionOn with
  | h f =>
    change (∀ᶠ n in U, f n ∈ cyclicWindow A (start n) (q n : ℕ)) at hx
    obtain ⟨n, hn, hdn, hfn, hsn⟩ := Filter.nonempty_of_mem
      (hx.and (hd.and ((eventually_eq_finiteValue U (fun n => naturalCyclicProjection (q n) h (f n))).and
        (eventually_eq_finiteValue U (fun n => (start n : ZMod (h : ℕ)))))))
    have hAn : start n + (f n).val ∈ A := (Finset.mem_filter.mp hn).2
    apply mem_residues.mpr
    refine ⟨start n + (f n).val, hAn, ?_⟩
    change ((start n + (f n).val : ℕ) : ZMod (h : ℕ)) =
      finiteValue U (fun n => naturalCyclicProjection (q n) h (f n)) +
        finiteValue U (fun n => (start n : ZMod (h : ℕ)))
    rw [Nat.cast_add, ← naturalCyclicProjection_val (q n) h hdn (f n), hfn, hsn, add_comm]

theorem actual_window_profile_zero_outside_residues
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (A : Set ℕ) (start : ℕ → ℕ)
    (r : ZMod (h : ℕ)) (hr : r ∉ residues (h : ℕ) A) :
    loebResidueProfile U hU q h
      (internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
      (r - finiteValue U (fun n => (start n : ZMod (h : ℕ)))) = 0 := by
  have heq : (internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) ∩
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹'
        {r - finiteValue U (fun n => (start n : ZMod (h : ℕ)))} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hmem := actual_residue_of_internal_cyclic_window U q h hd A start x hx.1
    have hφ : finiteQuotient U (fun n => naturalCyclicProjection (q n) h) x =
        r - finiteValue U (fun n => (start n : ZMod (h : ℕ))) := hx.2
    rw [hφ, sub_add_cancel] at hmem
    exact hr hmem
  unfold loebResidueProfile
  rw [heq, measure_empty, ENNReal.toReal_zero, mul_zero]

theorem sum_shifted_loebResidueProfile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (z : ZMod (h : ℕ)) :
    (∑ r, loebResidueProfile U hU q h S (r - z)) = (h : ℕ) * (loebMeasure U hU S).toReal := by
  calc
    (∑ r, loebResidueProfile U hU q h S (r - z)) = ∑ r, loebResidueProfile U hU q h S r := by
      apply Fintype.sum_equiv (Equiv.addRight (-z))
      intro r
      simp only [sub_eq_add_neg]
      rfl
    _ = _ := sum_loebResidueProfile U hU q h S

end Erdos335.Loeb

end
