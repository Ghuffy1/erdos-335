import Erdos335.LoebSparseOutput

/-!
# The one-sided reducible equality case

The conclusion supplies the two measurable exceptional pieces, their
periodic backgrounds, unique quotient expression, and exact inner sum
identity. The right exceptional piece has measure zero and is nonempty.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance oneSidedLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_one_sided_equality_reduction
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A Bcore B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBcorem : MeasurableSet Bcore) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU Bcore)
    (hBsub : Bcore ⊆ B) (hBmass : loebMeasure U hU B = loebMeasure U hU Bcore)
    (hcore : internalInnerMeasure U hU (A + Bcore) < loebMeasure U hU A + loebMeasure U hU Bcore)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU Bcore)
    (hnotperiod : ¬ (A + B) + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (A + Bcore) : Set _) =ᵐ[loebMeasure U hU] A + B) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + Bcore)
    ∃ a ∈ A, ∃ b ∈ B,
      let A₀ := A ∩ (a +ᵥ (H : Set G))
      let A₁ := A \ (a +ᵥ (H : Set G))
      let B₀ := B \ (Bcore + (H : Set G))
      let B₁ := B ∩ (Bcore + (H : Set G))
      MeasurableSet A₀ ∧ MeasurableSet A₁ ∧ MeasurableSet B₀ ∧ MeasurableSet B₁ ∧
      0 < loebMeasure U hU A₀ ∧ loebMeasure U hU A₀ < loebMeasure U hU (H : Set G) ∧
      loebMeasure U hU B₀ = 0 ∧ B₀.Nonempty ∧
      A = A₁ ∪ A₀ ∧ B = B₁ ∪ B₀ ∧
      A₀ ⊆ a +ᵥ (H : Set G) ∧ B₀ ⊆ b +ᵥ (H : Set G) ∧
      Disjoint (A₀ + (H : Set G)) A₁ ∧ Disjoint (B₀ + (H : Set G)) B₁ ∧
      loebMeasure U hU ((A₁ + (H : Set G)) \ A₁) = 0 ∧
      loebMeasure U hU ((B₁ + (H : Set G)) \ B₁) = 0 ∧
      (∀ x ∈ A, ∀ y ∈ B, x + y ∈ (a + b) +ᵥ (H : Set G) →
        x ∈ a +ᵥ (H : Set G) ∧ y ∈ b +ᵥ (H : Set G)) ∧
      internalInnerMeasure U hU (A₀ + B₀) = loebMeasure U hU A₀ + loebMeasure U hU B₀ := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let H := AddAction.stabilizer G (A + Bcore)
  obtain ⟨hCm, hHm, hHpos, _⟩ := loeb_measurable_kneser_identity U hU q A Bcore
    hAm hBcorem hApos hBpos hcore
  obtain ⟨a, ha, b, hb, hout, hApart, hactive, hBperiod, hAperiod⟩ :=
    loeb_nonperiodic_equality_extension_active_section U hU q A Bcore B
      hAm hBcorem hApos hBpos hBsub hcore hequality hnotperiod
  let A₀ := A ∩ (a +ᵥ (H : Set G))
  let A₁ := A \ (a +ᵥ (H : Set G))
  let B₀ := B \ (Bcore + (H : Set G))
  let B₁ := B ∩ (Bcore + (H : Set G))
  have hHperiod : (A + Bcore) + (H : Set G) = A + Bcore := by
    apply subset_antisymm
    · rintro z ⟨x, hx, k, hk, rfl⟩
      have hfix : k +ᵥ (A + Bcore) = A + Bcore := hk
      rw [← hfix]
      exact ⟨x, hx, add_comm k x⟩
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hbackground : A₁ + B ⊆ A + Bcore :=
    loeb_equality_extension_background_add_subset U hU q A Bcore B
      hAm hBcorem hApos hBpos hBsub hcore hequality a hactive hApart.2 hAperiod
  have hsparse : B₀ ⊆ b +ᵥ (H : Set G) :=
    loeb_equality_extension_sparse_subset_coset U hU q A Bcore B
      hAm hBcorem hApos hBpos hBsub hcore hequality a b ha hb hout hbackground
  have hsatm : MeasurableSet (Bcore + (H : Set G)) :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos Bcore
  have hA₀m : MeasurableSet A₀ := hAm.inter (measurable_loeb_coset U hU H hHm a)
  have hA₁m : MeasurableSet A₁ := hAm.diff (measurable_loeb_coset U hU H hHm a)
  have hB₀m : MeasurableSet B₀ := hBm.diff hsatm
  have hB₁m : MeasurableSet B₁ := hBm.inter hsatm
  have hB₀zero : μ B₀ = 0 := loeb_sparse_complement_measure_zero U hU q H Bcore B hBcorem hBsub hBmass
  have hB₀ne : B₀.Nonempty := by
    refine ⟨b, hb, ?_⟩
    rintro ⟨bcore, hbcore, k, hk, heq⟩
    apply hout
    rw [← hHperiod]
    refine ⟨a + bcore, add_mem_add ha hbcore, k, hk, ?_⟩
    change bcore + k = b at heq
    rw [← heq]
    abel
  have hAeq : A = A₁ ∪ A₀ := by
    ext x
    simp only [A₁, A₀, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hBeq : B = B₁ ∪ B₀ := by
    ext x
    simp only [B₁, B₀, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hAdisjoint : Disjoint (A₀ + (H : Set G)) A₁ := by
    apply Set.disjoint_left.mpr
    rintro x ⟨y, ⟨hyA, ⟨k, hk, hky⟩⟩, l, hl, hlx⟩ ⟨hxA, hxn⟩
    apply hxn
    refine ⟨k + l, H.add_mem hk hl, ?_⟩
    change a + k = y at hky
    change y + l = x at hlx
    change a + (k + l) = x
    rw [← add_assoc, hky, hlx]
  have hBdisjoint : Disjoint (B₀ + (H : Set G)) B₁ := by
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, k, hk, hky⟩ ⟨hxB, ⟨bcore, hbcore, l, hl, hlx⟩⟩
    apply hy.2
    refine ⟨bcore, hbcore, l - k, H.sub_mem hl hk, ?_⟩
    change y + k = x at hky
    change bcore + l = x at hlx
    change bcore + (l - k) = y
    calc
      _ = (bcore + l) - k := by abel
      _ = (y + k) - k := by rw [hlx, ← hky]
      _ = y := by simp
  have hB₁period : μ ((B₁ + (H : Set G)) \ B₁) = 0 :=
    loeb_inter_saturation_background_periodic U hU q H Bcore B hBsub hBperiod
  have hunique : ∀ x ∈ A, ∀ y ∈ B, x + y ∈ (a + b) +ᵥ (H : Set G) →
      x ∈ a +ᵥ (H : Set G) ∧ y ∈ b +ᵥ (H : Set G) := by
    intro x hx y hy hxy
    exact unique_expression_of_background_and_sparse H A Bcore B a b
      hHperiod hbackground hsparse hout x y hx hy hxy
  have hinner : internalInnerMeasure U hU (A₀ + B₀) = μ A₀ + μ B₀ := by
    rw [hB₀zero, add_zero]
    exact loeb_equality_extension_active_inner U hU q A Bcore B
      hAm hBcorem hApos hBpos hBsub hcore hequality a b hbackground hsparse hout hactive
  exact ⟨a, ha, b, hb, hA₀m, hA₁m, hB₀m, hB₁m, hApart.1, hApart.2, hB₀zero,
    hB₀ne, hAeq, hBeq, inter_subset_right, hsparse, hAdisjoint, hBdisjoint,
    hAperiod, hB₁period, hunique, hinner⟩

end Erdos335.Loeb

end
