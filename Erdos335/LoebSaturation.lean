import Erdos335.LoebInternal
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Countable saturation of internal sets

A nonprincipal ultrafilter on the natural numbers gives the finite
intersection property for countable families of internal sets. The proof
chooses representatives satisfying a growing finite list of conditions.
-/

set_option autoImplicit false

open Filter Set

namespace Erdos335.Loeb

variable {X : ℕ → Type*}

theorem exists_representative_of_eventually_finite [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ℕ → ∀ n, Set (X n))
    (hA : ∀ k, ∀ᶠ n in U, ∃ x : X n, ∀ j ≤ k, x ∈ A j n) :
    ∃ f : ∀ n, X n, ∀ j, ∀ᶠ n in U, f n ∈ A j n := by
  classical
  let P (n k : ℕ) : Prop := ∃ x : X n, ∀ j ≤ k, x ∈ A j n
  let best (n : ℕ) := Nat.findGreatest (P n) n
  let f : ∀ n, X n := fun n => if h : P n (best n) then h.choose else
    Classical.choice inferInstance
  refine ⟨f, fun j => ?_⟩
  have hge : ∀ᶠ n in U, j ≤ n := (eventually_ge_atTop j).filter_mono hU
  filter_upwards [hA j, hge] with n hnj hjn
  have hbest : P n (best n) := Nat.findGreatest_spec hjn hnj
  have hjbest : j ≤ best n := Nat.le_findGreatest hjn hnj
  change (if h : P n (best n) then h.choose else Classical.choice inferInstance) ∈ A j n
  rw [dite_eq_left hbest]
  exact hbest.choose_spec j hjbest

theorem countable_saturation [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ℕ → ∀ n, Set (X n))
    (hA : ∀ k, (⋂ j ≤ k, internalSet U (A j)).Nonempty) :
    (⋂ j, internalSet U (A j)).Nonempty := by
  have hfinite : ∀ k, ∀ᶠ n in U, ∃ x : X n, ∀ j ≤ k, x ∈ A j n := by
    intro k
    have hEq : internalSet U (fun n => {x | ∀ j ≤ k, x ∈ A j n}) =
        ⋂ j ≤ k, internalSet U (A j) := by
      have hfiber : (fun n => {x | ∀ j ≤ k, x ∈ A j n}) =
          (fun n => ⋂ j ≤ k, A j n) := by
        funext n
        ext x
        constructor
        · intro hx
          exact Set.mem_iInter.mpr fun j => Set.mem_iInter.mpr (hx j)
        · intro hx j hj
          exact Set.mem_iInter.mp (Set.mem_iInter.mp hx j) hj
      rw [hfiber]
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using
        internalSet_biInter_finset U (Finset.range (k + 1)) A
    exact (internalSet_nonempty_iff U _).mp (hEq.symm ▸ hA k)
  obtain ⟨f, hf⟩ := exists_representative_of_eventually_finite U hU A hfinite
  refine ⟨(f : (U : Filter ℕ).Product X), ?_⟩
  exact mem_iInter.mpr hf

theorem countable_saturation_internal [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : ℕ → Set ((U : Filter ℕ).Product X))
    (hS : ∀ k, S k ∈ internalSets U)
    (hfinite : ∀ k, (⋂ j ≤ k, S j).Nonempty) :
    (⋂ j, S j).Nonempty := by
  choose A hA using hS
  have hEq : S = fun k => internalSet U (A k) := funext fun k => (hA k).symm
  rw [hEq] at hfinite ⊢
  exact countable_saturation U hU A hfinite

theorem internal_countable_cover_has_finite [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (C : Set ((U : Filter ℕ).Product X))
    (V : ℕ → Set ((U : Filter ℕ).Product X))
    (hC : C ∈ internalSets U) (hV : ∀ k, V k ∈ internalSets U)
    (hcover : C ⊆ ⋃ k, V k) :
    ∃ m, C ⊆ ⋃ k ≤ m, V k := by
  classical
  by_contra! h
  let D (m : ℕ) := C \ ⋃ k ≤ m, V k
  have halg := isSetAlgebra_internalSets (X := X) U
  have hDmem : ∀ m, D m ∈ internalSets U := by
    intro m
    apply halg.sdiff_mem hC
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using
      halg.biUnion_mem (Finset.range (m + 1)) (fun k _ => hV k)
  have hDne : ∀ m, (D m).Nonempty := by
    intro m
    obtain ⟨x, hxC, hxV⟩ := Set.not_subset.mp (h m)
    exact ⟨x, hxC, hxV⟩
  have hfinite : ∀ m, (⋂ k ≤ m, D k).Nonempty := by
    intro m
    obtain ⟨x, hx⟩ := hDne m
    refine ⟨x, mem_iInter.mpr fun k => mem_iInter.mpr fun hkm => ?_⟩
    refine ⟨hx.1, ?_⟩
    intro hxk
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxk
    obtain ⟨hjk, hxj⟩ := mem_iUnion.mp hj
    exact hx.2 (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjk.trans hkm, hxj⟩⟩)
  obtain ⟨x, hx⟩ := countable_saturation_internal U hU D hDmem hfinite
  have hxC : x ∈ C := (mem_iInter.mp hx 0).1
  obtain ⟨k, hxk⟩ := mem_iUnion.mp (hcover hxC)
  exact (mem_iInter.mp hx k).2 (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨le_rfl, hxk⟩⟩)

end Erdos335.Loeb
