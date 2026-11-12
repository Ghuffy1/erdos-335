import Erdos335.LoebSparseCoset
import Erdos335.LoebInnerSplit

/-!
# The exact exceptional output of a one-sided equality reduction

The output outside the critical core consists exactly of the active input
section plus the sparse input section. Inner measure then gives their
required equality, including the zero-measure sparse summand.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem active_sparse_of_sum_not_mem
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (A B₀ B : Set G) (a x y : G)
    (hperiod : (A + B₀) + (H : Set G) = A + B₀)
    (hbackground : (A \ (a +ᵥ (H : Set G))) + B ⊆ A + B₀)
    (hx : x ∈ A) (hy : y ∈ B) (hout : x + y ∉ A + B₀) :
    x ∈ A ∩ (a +ᵥ (H : Set G)) ∧ y ∈ B \ (B₀ + (H : Set G)) := by
  have hxactive : x ∈ a +ᵥ (H : Set G) := by
    by_contra hn
    exact hout (hbackground ⟨x, ⟨hx, hn⟩, y, hy, rfl⟩)
  refine ⟨⟨hx, hxactive⟩, hy, ?_⟩
  rintro ⟨b₀, hb₀, k, hk, heq⟩
  apply hout
  rw [← hperiod]
  refine ⟨x + b₀, add_mem_add hx hb₀, k, hk, ?_⟩
  change b₀ + k = y at heq
  rw [← heq]
  abel

theorem sum_sdiff_eq_active_sparse
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (A B₀ B : Set G) (a b : G)
    (hperiod : (A + B₀) + (H : Set G) = A + B₀)
    (hbackground : (A \ (a +ᵥ (H : Set G))) + B ⊆ A + B₀)
    (hsparse : B \ (B₀ + (H : Set G)) ⊆ b +ᵥ (H : Set G))
    (hout : a + b ∉ A + B₀) :
    (A + B) \ (A + B₀) = (A ∩ (a +ᵥ (H : Set G))) + (B \ (B₀ + (H : Set G))) := by
  apply subset_antisymm
  · rintro z ⟨⟨x, hx, y, hy, rfl⟩, hz⟩
    obtain ⟨hxa, hys⟩ := active_sparse_of_sum_not_mem H A B₀ B a x y hperiod hbackground hx hy hz
    exact ⟨x, hxa, y, hys, rfl⟩
  · rintro z ⟨x, hx, y, hy, rfl⟩
    refine ⟨add_mem_add hx.1 hy.1, ?_⟩
    obtain ⟨k, hk, hkx⟩ := hx.2
    obtain ⟨l, hl, hly⟩ := hsparse hy
    intro hz
    apply hout
    rw [← hperiod]
    refine ⟨x + y, hz, -(k + l), H.neg_mem (H.add_mem hk hl), ?_⟩
    change a + k = x at hkx
    change b + l = y at hly
    rw [← hkx, ← hly]
    abel

theorem unique_expression_of_background_and_sparse
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (A B₀ B : Set G) (a b : G)
    (hperiod : (A + B₀) + (H : Set G) = A + B₀)
    (hbackground : (A \ (a +ᵥ (H : Set G))) + B ⊆ A + B₀)
    (hsparse : B \ (B₀ + (H : Set G)) ⊆ b +ᵥ (H : Set G))
    (hout : a + b ∉ A + B₀)
    (x y : G) (hx : x ∈ A) (hy : y ∈ B) (hxy : x + y ∈ (a + b) +ᵥ (H : Set G)) :
    x ∈ a +ᵥ (H : Set G) ∧ y ∈ b +ᵥ (H : Set G) := by
  have hnot : x + y ∉ A + B₀ := by
    intro hmem
    obtain ⟨k, hk, heq⟩ := hxy
    apply hout
    rw [← hperiod]
    refine ⟨x + y, hmem, -k, H.neg_mem hk, ?_⟩
    change (a + b) + k = x + y at heq
    rw [← heq]
    simp
  obtain ⟨hxa, hys⟩ := active_sparse_of_sum_not_mem H A B₀ B a x y hperiod hbackground hx hy hnot
  exact ⟨hxa.2, hsparse hys⟩

local instance sparseOutputLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_equality_extension_active_inner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B₀ B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hB₀m : MeasurableSet B₀)
    (hApos : 0 < loebMeasure U hU A) (hB₀pos : 0 < loebMeasure U hU B₀)
    (hB₀B : B₀ ⊆ B)
    (hcore : internalInnerMeasure U hU (A + B₀) < loebMeasure U hU A + loebMeasure U hU B₀)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B₀)
    (a b : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + B₀)
    (A \ (a +ᵥ (H : Set G))) + B ⊆ A + B₀ →
      B \ (B₀ + (H : Set G)) ⊆ b +ᵥ (H : Set G) →
      a + b ∉ A + B₀ →
      loebMeasure U hU A + loebMeasure U hU B₀ =
        loebMeasure U hU (A + B₀) + loebMeasure U hU (A ∩ (a +ᵥ (H : Set G))) →
      internalInnerMeasure U hU ((A ∩ (a +ᵥ (H : Set G))) + (B \ (B₀ + (H : Set G)))) =
        loebMeasure U hU (A ∩ (a +ᵥ (H : Set G))) := by
  dsimp only
  intro hbackground hsparse hout hactive
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let H := AddAction.stabilizer G (A + B₀)
  obtain ⟨hCm, _, _, _⟩ := loeb_measurable_kneser_identity U hU q A B₀ hAm hB₀m hApos hB₀pos hcore
  have hperiod : (A + B₀) + (H : Set G) = A + B₀ := by
    apply subset_antisymm
    · rintro z ⟨x, hx, k, hk, rfl⟩
      have hfix : k +ᵥ (A + B₀) = A + B₀ := hk
      rw [← hfix]
      exact ⟨x, hx, add_comm k x⟩
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hset := sum_sdiff_eq_active_sparse H A B₀ B a b hperiod hbackground hsparse hout
  have hsplit := internalInnerMeasure_eq_add_sdiff U hU (A + B) (A + B₀) hCm
    (add_subset_add (show A ⊆ A from Subset.rfl) hB₀B)
  rw [hset] at hsplit
  have heq := hsplit.symm.trans (hequality.trans hactive)
  apply le_antisymm
  · exact (ENNReal.add_le_add_iff_left (measure_ne_top μ (A + B₀))).mp heq.le
  · exact (ENNReal.add_le_add_iff_left (measure_ne_top μ (A + B₀))).mp heq.ge

theorem loeb_sparse_complement_measure_zero
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (B₀ B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hB₀m : MeasurableSet B₀) (hB₀B : B₀ ⊆ B)
    (hmass : loebMeasure U hU B = loebMeasure U hU B₀) :
    loebMeasure U hU (B \ (B₀ + (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))) = 0 := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hsub : B₀ ⊆ B₀ + (H : Set _) := by
    intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hzero : μ (B \ B₀) = 0 := by
    rw [measure_sdiff hB₀B hB₀m.nullMeasurableSet (measure_ne_top μ _), hmass, tsub_self]
  exact measure_mono_null (sdiff_subset_sdiff_right hsub) hzero

theorem loeb_inter_saturation_background_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (B₀ B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hB₀B : B₀ ⊆ B)
    (hperiod : loebMeasure U hU ((B₀ + (H : Set _)) \ B₀) = 0) :
    loebMeasure U hU (((B ∩ (B₀ + (H : Set _))) + (H : Set _)) \ (B ∩ (B₀ + (H : Set _)))) = 0 := by
  apply measure_mono_null _ hperiod
  rintro z ⟨⟨x, ⟨hxB, ⟨b₀, hb₀, k, hk, hkx⟩⟩, l, hl, hlz⟩, hz⟩
  have hzsat : z ∈ B₀ + (H : Set _) := by
    refine ⟨b₀, hb₀, k + l, H.add_mem hk hl, ?_⟩
    change b₀ + k = x at hkx
    change x + l = z at hlz
    change b₀ + (k + l) = z
    rw [← add_assoc, hkx, hlz]
  refine ⟨hzsat, ?_⟩
  intro hz₀
  exact hz ⟨hB₀B hz₀, hzsat⟩

end Erdos335.Loeb

end
