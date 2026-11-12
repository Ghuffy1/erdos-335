import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# An interval from almost-everywhere order convexity
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory

namespace Erdos335.Loeb

theorem ae_interval_of_order_convex_on_full_measure_set
    (S E : Set ℝ) (hS : S ⊆ Ioo 0 1) (hE : ∀ᵐ x : ℝ, x ∈ E)
    (hpositive : 0 < volume S)
    (hfill : ∀ a ∈ S ∩ E, ∀ b ∈ S ∩ E, ∀ x ∈ E, a < x → x < b → x ∈ S) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ S =ᵐ[volume] Ioo a b := by
  let T : Set ℝ := S ∩ E
  have hST : S =ᵐ[volume] T := by
    filter_upwards [hE] with x hx
    simp only [T, mem_inter_iff, hx, and_true]
  have hTpositive : 0 < volume T := by rwa [← measure_congr hST]
  have hT : T.Nonempty := nonempty_of_measure_ne_zero hTpositive.ne'
  have hlower : BddBelow T := ⟨0, fun x hx => (hS hx.1).1.le⟩
  have hupper : BddAbove T := ⟨1, fun x hx => (hS hx.1).2.le⟩
  let a := sInf T
  let b := sSup T
  have hzero : 0 ≤ a := le_csInf hT (fun x hx => (hS hx.1).1.le)
  have hone : b ≤ 1 := csSup_le hT (fun x hx => (hS hx.1).2.le)
  have hab : a < b := by
    apply lt_of_le_of_ne (csInf_le_csSup hT hlower hupper)
    intro heq
    have hsub : T ⊆ {a} := by
      intro x hx
      apply le_antisymm
      · have hxupper : x ≤ b := le_csSup hupper hx
        change a = b at heq
        rw [← heq] at hxupper
        exact hxupper
      · exact csInf_le hlower hx
    have hnull : volume T = 0 := measure_mono_null hsub (by simp)
    exact hTpositive.ne' hnull
  refine ⟨a, b, hzero, hab, hone, ?_⟩
  have hneA : ∀ᵐ x : ℝ, x ≠ a := by rw [ae_iff]; simp
  have hneB : ∀ᵐ x : ℝ, x ≠ b := by rw [ae_iff]; simp
  filter_upwards [hE, hneA, hneB] with x hxE hxa hxb
  apply propext
  constructor
  · intro hxS
    have hxT : x ∈ T := ⟨hxS, hxE⟩
    exact ⟨lt_of_le_of_ne (csInf_le hlower hxT) hxa.symm,
      lt_of_le_of_ne (le_csSup hupper hxT) hxb⟩
  · intro hx
    obtain ⟨u, hu, hux⟩ := exists_lt_of_csInf_lt hT hx.1
    obtain ⟨v, hv, hxv⟩ := exists_lt_of_lt_csSup hT hx.2
    exact hfill u hu v hv x hxE hux hxv

end Erdos335.Loeb
