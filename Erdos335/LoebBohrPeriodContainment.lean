import Erdos335.QuasiPeriodicPeriodRestriction

/-!
# A positive Bohr coset determines its containing finite period
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance bohrPeriodContainmentLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_circle_coset_period_le_of_ae_containment
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (H K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hKm : MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hKpos : 0 < loebMeasure U hU (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (S : Set (AddCircle (1 : ℝ))) (hSm : MeasurableSet S) (hSpos : 0 < volume S)
    (a b : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hcontain : (b +ᵥ (K : Set _)) ∩ φ ⁻¹' S ≤ᵐ[loebMeasure U hU] a +ᵥ (H : Set _)) :
    K ≤ H := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  intro k hk
  by_contra hkH
  obtain ⟨c, hcK, hcH⟩ : ∃ c : G, c ∈ b +ᵥ (K : Set G) ∧ c ∉ a +ᵥ (H : Set G) := by
    by_cases hb : b ∈ a +ᵥ (H : Set G)
    · refine ⟨b + k, ⟨k, hk, rfl⟩, ?_⟩
      rintro ⟨v, hv, hvbk⟩
      obtain ⟨u, hu, hub⟩ := hb
      apply hkH
      have hkuv : k = v - u := by
        change a + u = b at hub
        change a + v = b + k at hvbk
        rw [← hub] at hvbk
        apply add_left_cancel (a := a + u)
        calc
          (a + u) + k = a + v := hvbk.symm
          _ = (a + u) + (v - u) := by abel
      rw [hkuv]
      exact H.sub_mem hv hu
    · exact ⟨b, ⟨0, K.zero_mem, by simp⟩, hb⟩
  let J := H ⊓ K
  obtain ⟨hJm, hJpos⟩ := loeb_positive_subgroup_intersection U hU q H K hHm hKm hHpos hKpos
  have hsub : φ ⁻¹' S ∩ (c +ᵥ (J : Set G)) ⊆
      ((b +ᵥ (K : Set G)) ∩ φ ⁻¹' S) \ (a +ᵥ (H : Set G)) := by
    rintro x ⟨hxS, j, hj, rfl⟩
    obtain ⟨u, hu, huc⟩ := hcK
    refine ⟨⟨⟨u + j, K.add_mem hu hj.2, ?_⟩, hxS⟩, ?_⟩
    · change b + u = c at huc
      change b + (u + j) = c + j
      rw [← huc, add_assoc]
    · rintro ⟨v, hv, hvcj⟩
      apply hcH
      refine ⟨v - j, H.sub_mem hv hj.1, ?_⟩
      change a + v = c + j at hvcj
      change a + (v - j) = c
      calc
        a + (v - j) = (a + v) - j := by abel
        _ = c := by rw [hvcj]; abel
  have hzero : μ (φ ⁻¹' S ∩ (c +ᵥ (J : Set G))) = 0 :=
    measure_mono_null hsub (ae_le_set.mp hcontain)
  have hmass := loeb_circle_coset_intersection_measure U hU q φ hφ hsurj J hJm hJpos S hSm c
  have hpositive : 0 < μ (φ ⁻¹' S ∩ (c +ᵥ (J : Set G))) := by
    rw [hmass]
    exact ENNReal.mul_pos hJpos.ne' hSpos.ne'
  exact hpositive.ne' hzero

end Erdos335.Loeb

end
