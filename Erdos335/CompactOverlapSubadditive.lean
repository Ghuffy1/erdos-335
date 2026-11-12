import Erdos335.CompactSumLocalization

/-!
# Subadditivity of the loss of overlap under translation
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem haarOverlap_add_lower_bound
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (S : Set G) (hS : MeasurableSet S) (s t : G) :
    haarOverlap μ S s + haarOverlap μ S t ≤ (μ S).toReal + haarOverlap μ S (s + t) := by
  have hshift (u : G) : MeasurableSet (u +ᵥ S) := by
    rw [vadd_set_eq_neg_preimage]
    exact hS.preimage (measurable_const.add measurable_id)
  let A := S ∩ (s +ᵥ S)
  let B := (s +ᵥ S) ∩ ((s + t) +ᵥ S)
  have hBm : MeasurableSet B := (hshift s).inter (hshift (s + t))
  have hsubUnion : A ∪ B ⊆ s +ᵥ S := by
    rintro x (hx | hx)
    · exact hx.2
    · exact hx.1
  have hsubInter : A ∩ B ⊆ S ∩ ((s + t) +ᵥ S) :=
    fun _ hx => ⟨hx.1.1, hx.2.2⟩
  have hbound : μ A + μ B ≤ μ (s +ᵥ S) + μ (S ∩ ((s + t) +ᵥ S)) := by
    rw [← measure_union_add_inter A hBm]
    exact add_le_add (measure_mono hsubUnion) (measure_mono hsubInter)
  have hmassShift : μ (s +ᵥ S) = μ S := by
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have hBset : B = s +ᵥ (S ∩ (t +ᵥ S)) := by
    dsimp only [B]
    rw [vadd_set_inter, vadd_vadd]
  have hmassB : μ B = μ (S ∩ (t +ᵥ S)) := by
    rw [hBset, vadd_set_eq_neg_preimage, measure_preimage_add]
  have hreal := ENNReal.toReal_mono (by finiteness) hbound
  rw [ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ B),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hmassShift, hmassB] at hreal
  exact hreal

theorem haarOverlap_nsmul_loss_le
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (S : Set G) (hS : MeasurableSet S) (t : G) (n : ℕ) :
    (μ S).toReal - haarOverlap μ S (n • t) ≤
      n * ((μ S).toReal - haarOverlap μ S t) := by
  induction n with
  | zero => simp [haarOverlap]
  | succ n ih =>
    have hstep := haarOverlap_add_lower_bound μ S hS (n • t) t
    rw [succ_nsmul, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem haarOverlap_nsmul_loss_le_of_sumset
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (A B S : Set G) (hS : MeasurableSet S) (hsum : A + B ≤ᵐ[μ] S)
    (x y : G) (hx : x ∈ B) (hy : y ∈ B) (n : ℕ) :
    (μ S).toReal - haarOverlap μ S (n • (x - y)) ≤
      n * ((μ S).toReal - (μ A).toReal) := by
  have hsingle := haarOverlap_ge_of_sumset_ae_subset μ A B S hsum x y hx hy
  exact (haarOverlap_nsmul_loss_le μ S hS (x - y) n).trans
    (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))

end Erdos335.Loeb
