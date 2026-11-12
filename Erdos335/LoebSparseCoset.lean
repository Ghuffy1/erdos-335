import Erdos335.LoebEqualityBackgroundSums

/-!
# The sparse input in an equality extension

Once background sums remain in the critical core, every new input point
lies in the same exceptional coset. Positive measurable subgroups also
make arbitrary saturated sets measurable in the cyclic Loeb setting.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance sparseCosetLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem measurable_saturation_of_positive_subgroup
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) :
    MeasurableSet (A + (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  have hHH : (H : Set G) + (H : Set G) = H := by
    apply subset_antisymm
    · rintro x ⟨y, hy, z, hz, rfl⟩
      exact H.add_mem hy hz
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hperiod : (A + (H : Set G)) + (H : Set G) = A + (H : Set G) := by rw [add_assoc, hHH]
  obtain ⟨h, hH, _⟩ := positive_measurable_subgroup_eq_natural_kernel U hU q H hHm hHpos
  rw [hH] at hperiod ⊢
  obtain ⟨S, hS⟩ := exists_internalSet_of_natural_kernel_period U q h
    (A + (naturalCyclicKernel U q h : Set G)) hperiod
  rw [← hS]
  exact measurable_internalSet U _

theorem loeb_equality_extension_sparse_subset_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B₀ B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hB₀m : MeasurableSet B₀)
    (hApos : 0 < loebMeasure U hU A) (hB₀pos : 0 < loebMeasure U hU B₀)
    (hB₀B : B₀ ⊆ B)
    (hcore : internalInnerMeasure U hU (A + B₀) < loebMeasure U hU A + loebMeasure U hU B₀)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B₀)
    (a b : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (ha : a ∈ A) (hb : b ∈ B) (hout : a + b ∉ A + B₀) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + B₀)
    (A \ (a +ᵥ (H : Set G))) + B ⊆ A + B₀ →
      B \ (B₀ + (H : Set G)) ⊆ b +ᵥ (H : Set G) := by
  dsimp only
  intro hbackground
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let H := AddAction.stabilizer G (A + B₀)
  rintro t ⟨htB, htout⟩
  have hcore' : internalInnerMeasure U hU (B₀ + A) < loebMeasure U hU B₀ + loebMeasure U hU A := by
    simpa only [add_comm] using hcore
  have hex : ∃ c ∈ A, c + t ∉ A + B₀ := by
    by_contra hn
    have hsub : t +ᵥ A ⊆ B₀ + A := by
      rintro x ⟨c, hc, rfl⟩
      rw [add_comm B₀ A]
      by_contra hx
      apply hn
      refine ⟨c, hc, ?_⟩
      simpa only [vadd_eq_add, add_comm] using hx
    have hzero : loebMeasure U hU ((t +ᵥ A) \ (B₀ + A)) = 0 := by
      rw [sdiff_eq_empty.mpr hsub, measure_empty]
    have hmem := loeb_critical_translate_maximal U hU q B₀ A hB₀m hAm hB₀pos hApos hcore' t hzero
    rw [add_comm B₀ A] at hmem
    exact htout hmem
  obtain ⟨c, hc, hcout⟩ := hex
  have hca : c ∈ a +ᵥ (H : Set G) := by
    by_contra hn
    exact hcout (hbackground ⟨c, ⟨hc, hn⟩, t, htB, rfl⟩)
  obtain ⟨k, hk, hkc⟩ := hca
  have hdiff := loeb_equality_extension_extra_outputs_same_coset U hU q A B₀ B
    hAm hB₀m hApos hB₀pos hB₀B hcore hequality c a t b hc ha htB hb hcout hout
  have htb : t - b ∈ H := by
    have hh := H.sub_mem hdiff hk
    have heq : ((c + t) - (a + b)) - k = t - b := by
      change a + k = c at hkc
      rw [← hkc]
      abel
    rwa [heq] at hh
  exact ⟨t - b, htb, by simp [vadd_eq_add]⟩

end Erdos335.Loeb

end
