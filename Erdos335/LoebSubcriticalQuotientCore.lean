import Erdos335.LoebSubcritical
import Erdos335.LoebLiteralResidues
import Erdos335.NaturalCyclicProjection

/-!
# Exact finite quotient cores of strictly subcritical internal pairs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance subcriticalQuotientCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_saturated_critical_cardinality
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ))
    (hp : ∀ᶠ n in U, Function.Surjective (p n))
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (S T : Finset (ZMod (h : ℕ)))
    (hS : (finiteQuotient U p) '' A = (S : Set _))
    (hT : (finiteQuotient U p) '' B = (T : Set _))
    (hsat : A + B + ((finiteQuotient U p).ker : Set _) = A + B)
    (hidentity : loebMeasure U hU (A + ((finiteQuotient U p).ker : Set _)) +
      loebMeasure U hU (B + ((finiteQuotient U p).ker : Set _)) =
        loebMeasure U hU (A + B) + loebMeasure U hU
          ((finiteQuotient U p).ker : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    (S + T).card + 1 = S.card + T.card := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let φ : G →+ ZMod (h : ℕ) := finiteQuotient U p
  have mass (C : Set G)
      (R : Finset (ZMod (h : ℕ))) (hR : φ '' C = (R : Set _)) :
      (μ (C + (φ.ker : Set G))).toReal = (R.card : ℝ) / (h : ℕ) := by
    rw [addHom_saturation_eq_preimage_image, hR,
      loebMeasure_finiteQuotient_preimage U hU q p hp,
      ENNReal.toReal_div, ENNReal.toReal_natCast]
    simp
  have hC : φ '' (A + B) = (S + T : Finset (ZMod (h : ℕ))) := by
    rw [Set.image_add, hS, hT, Finset.coe_add]
  have hAmass := mass A S hS
  have hBmass := mass B T hT
  have hCmass' := mass (A + B) (S + T) hC
  have hCmass : (μ (A + B)).toReal = ((S + T).card : ℝ) / (h : ℕ) := by
    exact (congrArg (fun X : Set G => (μ X).toReal) hsat.symm).trans hCmass'
  have hHmass : (μ (φ.ker : Set G)).toReal = (1 : ℝ) / (h : ℕ) := by
    rw [finiteQuotient_ker, loebMeasure_internalSubgroup_of_eventually_quotients U hU p hp]
    simp
  have hreal := congrArg ENNReal.toReal hidentity
  change (μ (A + (φ.ker : Set G)) + μ (B + (φ.ker : Set G))).toReal =
    (μ (A + B) + μ (φ.ker : Set G)).toReal at hreal
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    hAmass, hBmass, hCmass, hHmass] at hreal
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  field_simp [hh] at hreal
  exact_mod_cast hreal.symm

theorem exists_loeb_subcritical_quotient_core
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : ∀ n, Set (ZMod (q n : ℕ)))
    (hA : (internalSet U A).Nonempty) (hB : (internalSet U B).Nonempty)
    (hsmall : loebMeasure U hU (internalSet U (fun n => A n + B n)) <
      loebMeasure U hU (internalSet U A) + loebMeasure U hU (internalSet U B)) :
    ∃ (h : ℕ+) (S T : Finset (ZMod (h : ℕ))),
      (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) '' internalSet U A = (S : Set _) ∧
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) '' internalSet U B = (T : Set _) ∧
      internalSet U (fun n => A n + B n) =
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (S + T : Finset _) ∧
      (S + T).card + 1 = S.card + T.card := by
  classical
  let K := fun n => AddAction.stabilizer (ZMod (q n : ℕ)) (A n + B n)
  have hKpos := subcritical_stabilizer_positive U hU A B hA hB hsmall
  rw [← internalAddSubgroup_stabilizer] at hKpos
  obtain ⟨D, hD⟩ := eventually_bounded_index_of_positive_loebMeasure U hU K hKpos
  obtain ⟨h, p, hDh, hp, hker⟩ := exists_fixed_natural_cyclic_quotient U q K D hD
  have hd := hp.mono fun n hn => hn.1
  have hnat := hp.mono fun n hn => hn.2.2.2
  have hnat' : ∀ᶠ n in U, ∀ t : ℕ,
      naturalCyclicProjection (q n) h (t : ZMod (q n : ℕ)) = (t : ZMod (h : ℕ)) :=
    hd.mono fun n hn t => naturalCyclicProjection_natCast (q n) h hn t
  have heq := finiteQuotient_eq_of_eventually_natural U q h p
    (fun n => naturalCyclicProjection (q n) h) hnat hnat'
  rw [heq] at hker
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  let C := internalSet U (fun n => A n + B n)
  have hK : φ.ker = AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) C := by
    exact hker.trans (internalAddSubgroup_stabilizer U (fun n => A n + B n))
  have hsat : C + (φ.ker : Set _) = C := by
    apply subset_antisymm
    · rintro x ⟨c, hc, k, hk, rfl⟩
      rw [hK] at hk
      have he : k +ᵥ C = C := hk
      have hm : k + c ∈ k +ᵥ C := ⟨c, hc, rfl⟩
      rw [he] at hm
      simpa only [add_comm] using hm
    · intro x hx
      exact ⟨x, hx, 0, φ.ker.zero_mem, add_zero x⟩
  let S := (φ '' internalSet U A).toFinite.toFinset
  let T := (φ '' internalSet U B).toFinite.toFinset
  have hS : φ '' internalSet U A = (S : Set _) := by ext x; simp [S]
  have hT : φ '' internalSet U B = (T : Set _) := by ext x; simp [T]
  have himage : φ '' C = (S + T : Finset (ZMod (h : ℕ))) := by
    change φ '' internalSet U (fun n => A n + B n) = _
    rw [internalSet_add, Set.image_add, hS, hT, Finset.coe_add]
  have hCpre : C = φ ⁻¹' (S + T : Finset (ZMod (h : ℕ))) := by
    calc
      C = C + (φ.ker : Set _) := hsat.symm
      _ = φ ⁻¹' (φ '' C) := addHom_saturation_eq_preimage_image φ C
      _ = _ := congrArg (fun R : Set (ZMod (h : ℕ)) => φ ⁻¹' R) himage
  have hidentity := loebMeasure_critical_identity U hU A B hA hB hsmall
  dsimp only at hidentity
  rw [← hker] at hidentity
  change internalSet U (fun n => A n + B n) + (φ.ker : Set _) =
    internalSet U (fun n => A n + B n) at hsat
  rw [internalSet_add] at hsat
  rw [internalSet_add] at hidentity
  have hsurj := hd.mono fun n hn => naturalCyclicProjection_surjective (q n) h hn
  exact ⟨h, S, T, hd, hS, hT, hCpre,
    loeb_saturated_critical_cardinality U hU q h (fun n => naturalCyclicProjection (q n) h)
      hsurj (internalSet U A) (internalSet U B) S T hS hT hsat hidentity⟩

end Erdos335.Loeb

end
