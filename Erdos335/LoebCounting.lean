import Erdos335.LoebInternal
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.Tactic

/-!
# The internal counting content

Normalized finite counting ratios have ultralimits in the compact extended
nonnegative real line. Equality of internal sets gives the same ultralimit.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

noncomputable def countingRatio {Y : Type*} (A : Set Y) : ℝ≥0∞ :=
  (A.ncard : ℝ≥0∞) / (Nat.card Y : ℝ≥0∞)

theorem countingRatio_empty {Y : Type*} : countingRatio (∅ : Set Y) = 0 := by
  simp [countingRatio]

theorem countingRatio_univ {Y : Type*} [Finite Y] [Nonempty Y] :
    countingRatio (univ : Set Y) = 1 := by
  have hcard : (Nat.card Y : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  simpa only [countingRatio, Set.ncard_univ] using ENNReal.div_self hcard (by simp)

theorem countingRatio_le_one {Y : Type*} [Finite Y] (A : Set Y) :
    countingRatio A ≤ 1 := by
  have hle : (A.ncard : ℝ≥0∞) ≤ (Nat.card Y : ℝ≥0∞) := by
    exact_mod_cast Set.ncard_le_card A
  calc
    countingRatio A ≤ (Nat.card Y : ℝ≥0∞) / (Nat.card Y : ℝ≥0∞) :=
      ENNReal.div_le_div_right hle _
    _ ≤ 1 := ENNReal.div_self_le_one

theorem countingRatio_union {Y : Type*} [Finite Y] (A B : Set Y)
    (h : Disjoint A B) : countingRatio (A ∪ B) = countingRatio A + countingRatio B := by
  simp only [countingRatio, Set.ncard_union_eq h, Nat.cast_add, ENNReal.add_div]

variable {I : Type*} {X : I → Type*}

noncomputable def ultraCount (U : Ultrafilter I) (A : ∀ i, Set (X i)) : ℝ≥0∞ :=
  (U.map (fun i => countingRatio (A i))).lim

theorem tendsto_ultraCount (U : Ultrafilter I) (A : ∀ i, Set (X i)) :
    Tendsto (fun i => countingRatio (A i)) (U : Filter I) (𝓝 (ultraCount U A)) := by
  exact (U.map (fun i => countingRatio (A i))).le_nhds_lim

theorem ultraCount_congr (U : Ultrafilter I) (A B : ∀ i, Set (X i))
    (h : ∀ᶠ i in U, A i = B i) : ultraCount U A = ultraCount U B := by
  apply tendsto_nhds_unique (tendsto_ultraCount U A)
  exact (tendsto_ultraCount U B).congr' (h.mono fun i hi => congrArg countingRatio hi.symm)

theorem ultraCount_empty (U : Ultrafilter I) :
    ultraCount U (fun i => (∅ : Set (X i))) = 0 := by
  apply tendsto_nhds_unique (tendsto_ultraCount U _)
  simpa only [countingRatio_empty] using
    (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℝ≥0∞)) (U : Filter I) (𝓝 0))

theorem ultraCount_univ [∀ i, Finite (X i)] [∀ i, Nonempty (X i)] (U : Ultrafilter I) :
    ultraCount U (fun i => (univ : Set (X i))) = 1 := by
  apply tendsto_nhds_unique (tendsto_ultraCount U _)
  simpa only [countingRatio_univ] using
    (tendsto_const_nhds : Tendsto (fun _ : I => (1 : ℝ≥0∞)) (U : Filter I) (𝓝 1))

theorem ultraCount_le_one [∀ i, Finite (X i)]
    (U : Ultrafilter I) (A : ∀ i, Set (X i)) : ultraCount U A ≤ 1 :=
  le_of_tendsto (tendsto_ultraCount U A) (.of_forall fun i => countingRatio_le_one (A i))

theorem ultraCount_union [∀ i, Finite (X i)] (U : Ultrafilter I)
    (A B : ∀ i, Set (X i)) (h : ∀ᶠ i in U, Disjoint (A i) (B i)) :
    ultraCount U (fun i => A i ∪ B i) = ultraCount U A + ultraCount U B := by
  apply tendsto_nhds_unique (tendsto_ultraCount U _)
  exact ((tendsto_ultraCount U A).add (tendsto_ultraCount U B)).congr'
    (h.mono fun i hi => (countingRatio_union (A i) (B i) hi).symm)

noncomputable def internalMass (U : Ultrafilter I)
    (S : Set ((U : Filter I).Product X)) : ℝ≥0∞ := by
  classical
  exact if h : S ∈ internalSets U then ultraCount U h.choose else 0

theorem internalMass_internal [∀ i, Nonempty (X i)] (U : Ultrafilter I)
    (A : ∀ i, Set (X i)) : internalMass U (internalSet U A) = ultraCount U A := by
  classical
  have h : internalSet U A ∈ internalSets U := ⟨A, rfl⟩
  rw [internalMass, dite_eq_left h]
  apply ultraCount_congr
  exact (internalSet_eq_iff U _ A).mp h.choose_spec

theorem internalMass_empty [∀ i, Nonempty (X i)] (U : Ultrafilter I) :
    internalMass (X := X) U ∅ = 0 := by
  rw [← internalSet_empty (X := X) U, internalMass_internal, ultraCount_empty]

theorem internalMass_univ [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (U : Ultrafilter I) : internalMass (X := X) U univ = 1 := by
  rw [← internalSet_univ (X := X) U, internalMass_internal, ultraCount_univ]

theorem internalMass_le_one [∀ i, Finite (X i)]
    (U : Ultrafilter I) (S : Set ((U : Filter I).Product X)) : internalMass U S ≤ 1 := by
  classical
  unfold internalMass
  split
  · exact ultraCount_le_one U _
  · exact zero_le

theorem internalMass_union [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (U : Ultrafilter I) {S T : Set ((U : Filter I).Product X)}
    (hS : S ∈ internalSets U) (hT : T ∈ internalSets U) (h : Disjoint S T) :
    internalMass U (S ∪ T) = internalMass U S + internalMass U T := by
  obtain ⟨A, rfl⟩ := hS
  obtain ⟨B, rfl⟩ := hT
  have hEq : internalSet U (fun i => A i ∩ B i) =
      internalSet U (fun i => (∅ : Set (X i))) := by
    rw [internalSet_inter, Set.disjoint_iff_inter_eq_empty.mp h, internalSet_empty]
  have hAB : ∀ᶠ i in U, Disjoint (A i) (B i) :=
    ((internalSet_eq_iff U _ _).mp hEq).mono fun i hi =>
      Set.disjoint_iff_inter_eq_empty.mpr hi
  rw [← internalSet_union, internalMass_internal, internalMass_internal, internalMass_internal]
  exact ultraCount_union U A B hAB

noncomputable def internalCountingContent [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (U : Ultrafilter I) : AddContent ℝ≥0∞ (internalSets (X := X) U) :=
  (isSetAlgebra_internalSets (X := X) U).isSetRing.addContent_of_union
    (internalMass U) (internalMass_empty U) (internalMass_union U)

theorem internalCountingContent_apply [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (U : Ultrafilter I) (S : Set ((U : Filter I).Product X)) :
    internalCountingContent U S = internalMass U S := rfl

theorem internalCountingContent_internal [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (U : Ultrafilter I) (A : ∀ i, Set (X i)) :
    internalCountingContent U (internalSet U A) = ultraCount U A :=
  internalMass_internal U A

end Erdos335.Loeb
