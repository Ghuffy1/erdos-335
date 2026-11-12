import Erdos335.LoebCosetSectionSums
import Erdos335.LoebInnerAE

/-!
# One exceptional output coset from a noncritical component

The per-coset deficit bounds in the Dyson argument force all output outside
the periodic part into one coset once a noncritical component is present.
The proof compares two disjoint output sections with their input sections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance singleOutsideCosetLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_single_outside_coset_of_noncritical_section
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (A B S T : Set ((U : Filter ℕ).Product X))
    (hSm : MeasurableSet S)
    (hsplit : S = T ∪ (A + B)) (hperiod : T + (H : Set _) = T)
    (hsame : A + (H : Set _) = B + (H : Set _))
    (hstrict : loebMeasure U hU T < loebMeasure U hU S)
    (hbound : ∀ a ∈ A, loebMeasure U hU S ≤ loebMeasure U hU T +
      (loebMeasure U hU (A ∩ (a +ᵥ (H : Set _))) +
        loebMeasure U hU (B ∩ (a +ᵥ (H : Set _)))))
    (i j : (U : Filter ℕ).Product X) (hi : i ∈ A) (hj : j ∈ A)
    (hout : i + j ∉ T)
    (hcritical : loebMeasure U hU (A ∩ (i +ᵥ (H : Set _))) +
      loebMeasure U hU (B ∩ (j +ᵥ (H : Set _))) ≤
        internalInnerMeasure U hU
          ((A ∩ (i +ᵥ (H : Set _))) + (B ∩ (j +ᵥ (H : Set _))))) :
    S \ T ⊆ (i + j) +ᵥ (H : Set _) := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let f (x : G) := (μ (A ∩ (x +ᵥ (H : Set G)))).toReal
  let g (x : G) := (μ (B ∩ (x +ᵥ (H : Set G)))).toReal
  let r (x : G) := (μ (S ∩ (x +ᵥ (H : Set G)))).toReal
  let δ := (μ S).toReal - (μ T).toReal
  have hδpos : 0 < δ := sub_pos.mpr
    ((ENNReal.toReal_lt_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr hstrict)
  have hTS : T ⊆ S := by rw [hsplit]; exact subset_union_left
  have hAS : A + B ⊆ S := by rw [hsplit]; exact subset_union_right
  have hnonemptyA (x : G) (hx : x ∈ A) : (A ∩ (x +ᵥ (H : Set G))).Nonempty :=
    ⟨x, hx, 0, H.zero_mem, by simp⟩
  have hnonemptyB (x : G) (hx : x ∈ B) : (B ∩ (x +ᵥ (H : Set G))).Nonempty :=
    ⟨x, hx, 0, H.zero_mem, by simp⟩
  have hinput (x y : G) (hx : (A ∩ (x +ᵥ (H : Set G))).Nonempty)
      (hy : (B ∩ (y +ᵥ (H : Set G))).Nonempty) :
      f x ≤ r (x + y) ∧ g y ≤ r (x + y) := by
    obtain ⟨hleft, hright⟩ := loeb_section_measures_le_sum_section U hU H A B S hAS x y hx hy
    exact ⟨ENNReal.toReal_mono (measure_ne_top μ _) hleft,
      ENNReal.toReal_mono (measure_ne_top μ _) hright⟩
  have hδbound (x : G) (hx : x ∈ A) : δ ≤ f x + g x := by
    have h := ENNReal.toReal_mono (by finiteness) (hbound x hx)
    rw [ENNReal.toReal_add (measure_ne_top μ _) (by finiteness),
      ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h
    change (μ S).toReal ≤ (μ T).toReal + (f x + g x) at h
    dsimp only [δ]
    linarith
  have hcrit : f i + g j ≤ r (i + j) := by
    have h := hcritical.trans ((internalInnerMeasure_le U hU _).trans
      (measure_mono (coset_section_sum_subset H A B S hAS i j)))
    have hr := ENNReal.toReal_mono (measure_ne_top μ _) h
    rwa [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hr
  have hij := hinput i j (hnonemptyA i hi) (coset_section_nonempty_of_saturation_eq H A B hsame j hj)
  have hji := hinput j i (hnonemptyA j hj) (coset_section_nonempty_of_saturation_eq H A B hsame i hi)
  rw [add_comm j i] at hji
  rintro z ⟨hzS, hzT⟩
  by_contra hn
  obtain ⟨a, ha, b, hb, hab⟩ := (hsplit ▸ hzS).resolve_left hzT
  subst z
  let R₁ := S ∩ ((i + j) +ᵥ (H : Set G))
  let R₂ := S ∩ ((a + b) +ᵥ (H : Set G))
  have hR₁m : MeasurableSet R₁ := hSm.inter (measurable_loeb_coset U hU H hHm _)
  have hR₂m : MeasurableSet R₂ := hSm.inter (measurable_loeb_coset U hU H hHm _)
  have hd₁ : Disjoint T R₁ := (disjoint_periodic_set_coset H T hperiod _ hout).mono_right inter_subset_right
  have hd₂ : Disjoint T R₂ := (disjoint_periodic_set_coset H T hperiod _ hzT).mono_right inter_subset_right
  have hd₁₂ : Disjoint R₁ R₂ := (disjoint_cosets_of_not_mem H (i + j) (a + b) hn).mono
    inter_subset_right inter_subset_right
  have hmeasure : (μ T + μ R₁) + μ R₂ ≤ μ S := by
    rw [← measure_union hd₁ hR₁m, ← measure_union (hd₂.union_left hd₁₂) hR₂m]
    exact measure_mono (union_subset (union_subset hTS inter_subset_left) inter_subset_left)
  have htotal : r (i + j) + r (a + b) ≤ δ := by
    have h := ENNReal.toReal_mono (measure_ne_top μ _) hmeasure
    rw [ENNReal.toReal_add (by finiteness) (measure_ne_top μ _),
      ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h
    change ((μ T).toReal + r (i + j)) + r (a + b) ≤ (μ S).toReal at h
    dsimp only [δ]
    linarith
  have habounds := hinput a b (hnonemptyA a ha) (hnonemptyB b hb)
  have hbabounds := hinput b a
    (coset_section_nonempty_of_saturation_eq H B A hsame.symm b hb)
    (coset_section_nonempty_of_saturation_eq H A B hsame a ha)
  rw [add_comm b a] at hbabounds
  have hdi := hδbound i hi
  have hdj := hδbound j hj
  have hda := hδbound a ha
  linarith [hij.1, hij.2, hji.1, hji.2, habounds.1, hbabounds.2]

end Erdos335.Loeb

end
