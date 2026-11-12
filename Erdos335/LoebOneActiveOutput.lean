import Erdos335.LoebFiniteNoncriticalComponent

/-!
# A noncritical component outside a periodic background

The active input occupies one coset. A finite coset cover of the other
input isolates a noncritical component whose output lies outside the
periodic background.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance oneActiveOutputLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_noncritical_section_outside_periodic_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (A₀ B S T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A₀) (hBm : MeasurableSet B)
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (ha : a ∈ A₀)
    (hAcoset : A₀ ⊆ a +ᵥ (H : Set _))
    (hsplit : S = T ∪ (A₀ + B)) (hperiod : T + (H : Set _) = T)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧ S + (L : Set _) = S) :
    ∃ b ∈ B, a + b ∉ T ∧
      loebMeasure U hU A₀ + loebMeasure U hU (B ∩ (b +ᵥ (H : Set _))) ≤
        internalInnerMeasure U hU (A₀ + (B ∩ (b +ᵥ (H : Set _)))) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  obtain ⟨R, hRB, hcover⟩ := loeb_exists_finite_coset_cover U hU q H hHm hHpos B
  let I := {b : R // a + (b : G) ∉ T}
  let C (i : I) : Set G := B ∩ ((i.val : G) +ᵥ (H : Set G))
  have hCm (i : I) : MeasurableSet (C i) := hBm.inter (measurable_loeb_coset U hU H hHm _)
  have hCne (i : I) : (C i).Nonempty := ⟨i.val, hRB i.val.property, 0, H.zero_mem, by simp⟩
  have hdecomp : S = T ∪ ⋃ i : I, A₀ + C i := by
    ext z
    constructor
    · intro hz
      by_cases hzT : z ∈ T
      · exact Or.inl hzT
      obtain ⟨x, hx, y, hy, hxy⟩ := (hsplit ▸ hz).resolve_left hzT
      have hyR : y ∈ (R : Set G) + (H : Set G) := by
        rw [← hcover]
        exact ⟨y, hy, 0, H.zero_mem, add_zero y⟩
      obtain ⟨b, hb, k, hk, hky⟩ := hyR
      obtain ⟨l, hl, hlx⟩ := hAcoset hx
      have hout : a + b ∉ T := by
        intro hab
        apply hzT
        have hmem : z ∈ T + (H : Set G) := by
          refine ⟨a + b, hab, l + k, H.add_mem hl hk, ?_⟩
          change a + l = x at hlx
          change b + k = y at hky
          calc
            (a + b) + (l + k) = (a + l) + (b + k) := by abel
            _ = z := by rw [hlx, hky]; exact hxy
        rwa [hperiod] at hmem
      let i : I := ⟨⟨b, hb⟩, hout⟩
      exact Or.inr (mem_iUnion.mpr ⟨i, x, hx, y, ⟨hy, k, hk, hky⟩, hxy⟩)
    · rintro (hzT | hz)
      · rw [hsplit]
        exact Or.inl hzT
      · obtain ⟨i, x, hx, y, hy, hxy⟩ := mem_iUnion.mp hz
        rw [hsplit]
        exact Or.inr ⟨x, hx, y, hy.1, hxy⟩
  have hnotperiod' : ¬ ∃ L : AddSubgroup G, MeasurableSet (L : Set G) ∧
      0 < μ (L : Set G) ∧ (T ∪ ⋃ i : I, A₀ + C i) + (L : Set G) = T ∪ ⋃ i : I, A₀ + C i := by
    intro h
    apply hnotperiod
    rwa [← hdecomp] at h
  obtain ⟨i, hi⟩ := loeb_nonperiodic_union_base_has_noncritical_component U hU q
    (fun _ : I => A₀) C (fun _ => hAm) hCm (fun _ => ⟨a, ha⟩) hCne T H hHm hHpos hperiod hnotperiod'
  exact ⟨i.val, hRB i.val.property, i.property, hi⟩

end Erdos335.Loeb

end
