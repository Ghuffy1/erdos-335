import Erdos335.LoebFiniteQuotient
import Mathlib.Data.Int.Interval

/-!
# Bounded and divergent integral drifts along an ultrafilter
-/

set_option autoImplicit false

open Filter Set Topology

noncomputable section

namespace Erdos335.Loeb

private theorem eventually_constant_of_finite_values
    {ι α : Type*} (U : Ultrafilter ι) (f : ι → α) (F : Finset α)
    (hF : ∀ᶠ i in U, f i ∈ F) :
    ∃ a : α, ∀ᶠ i in U, f i = a := by
  classical
  obtain ⟨i₀, hi₀⟩ := hF.exists
  let g : ι → (F : Set α) := fun i =>
    if hi : f i ∈ F then ⟨f i, hi⟩ else ⟨f i₀, hi₀⟩
  refine ⟨(finiteValue U g).val, ?_⟩
  filter_upwards [hF, eventually_eq_finiteValue U g] with i hi hgi
  have hval := congrArg Subtype.val hgi
  simpa only [g, dif_pos hi] using hval

theorem integer_drift_constant_or_diverges
    {ι : Type*} (U : Ultrafilter ι) (d : ι → ℤ) :
    (∃ k : ℤ, ∀ᶠ i in U, d i = k) ∨
      Tendsto (fun i => (d i).natAbs) (U : Filter ι) atTop := by
  classical
  by_cases hbounded : ∃ N : ℕ, ∀ᶠ i in U, (d i).natAbs ≤ N
  · obtain ⟨N, hN⟩ := hbounded
    apply Or.inl
    apply eventually_constant_of_finite_values U d (Finset.Icc (-(N : ℤ)) (N : ℤ))
    filter_upwards [hN] with i hi
    apply Finset.mem_Icc.mpr
    have habs : |d i| ≤ (N : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hi
    exact abs_le.mp habs
  · apply Or.inr
    apply tendsto_atTop.mpr
    intro N
    have hnot : ¬ ∀ᶠ i in U, (d i).natAbs ≤ N := fun h => hbounded ⟨N, h⟩
    have hgreater := Ultrafilter.eventually_not.mpr hnot
    exact hgreater.mono fun i hi => (lt_of_not_ge hi).le

end Erdos335.Loeb

end
